#![cfg_attr(not(test), no_std)]

use core::ffi::c_uint;
use crc::Crc;
use bit::BitIndex;

pub const MAX_FRAME_SIZE: usize = 10;
pub const MAX_PACKET_SIZE: usize = 126;
const CRC: crc::Crc<u16> = crc::Crc::<u16>::new(&crc::CRC_16_MODBUS);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanDudeFrame {
    pub address: u8,
    pub data: arrayvec::ArrayVec<u8, MAX_FRAME_SIZE>,
    pub counter: u8,
    pub end_of_packet: bool,
}

impl CanDudeFrame {
    pub fn from_canbus(id: u32, data: &[u8]) -> Option<Self> {
        let address = id as u8 & 0b11_111;
        let end_of_packet = ((id >> 5) as u8 & 0b1) == 1;

        let counter = (id >> 6) as u8 & 0b111_1111;

        let mut arr: arrayvec::ArrayVec<u8, MAX_FRAME_SIZE> = arrayvec::ArrayVec::new();
        arr.push((id >> 13) as u8);
        arr.push((id >> (13 + 8)) as u8);
        arr.try_extend_from_slice(data).ok()?;

        Some(Self {
            address,
            data: arr,
            counter,
            end_of_packet,
        })
    }

    pub fn to_canbus(&self) -> (u32, &[u8]) {
        let mut id: u32 = (self.address & 0b11111) as u32;
        id |= (self.end_of_packet as u32 & 1) << 5;
        id |= (self.counter as u32 & 0b111_1111) << 6;

        let mut iter = self.data.iter();
        if let Some(v) = iter.next() {
            id |= (*v as u32) << 13;
        }
        if let Some(v) = iter.next() {
            id |= (*v as u32) << (13 + 8);
        }

        let data = iter.as_slice();

        (id, data)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SizeType {
    SingleFrame,
    MultiFrame,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanDudePacketSender<'a> {
    address: u8,
    data: &'a [u8],
    sent_counter: usize, // with len and crc
    crc: [u8; 2],
}

impl<'a> CanDudePacketSender<'a> {
    pub fn new<'b: 'a, T>(address: u8, data: &'b T) -> Option<Self>
    where
        T: AsRef<[u8]>,
    {
        let data = data.as_ref();
        (!data.is_empty() || data.len() > MAX_PACKET_SIZE).then_some(())?;

        Some(Self {
            address,
            data,
            sent_counter: 0,
            crc: CRC.checksum(data).to_be_bytes(),
        })
    }

    pub fn address(&self) -> u8 {
        self.address
    }

    pub fn completed(&self) -> bool {
        match self.size_type() {
            SizeType::SingleFrame => self.sent_counter >= self.data.len(),
            SizeType::MultiFrame => self.sent_counter >= self.data.len() + 2,
        }
    }

    pub fn size_type(&self) -> SizeType {
        match self.data.len() {
            0..=MAX_FRAME_SIZE => SizeType::SingleFrame,
            11..=MAX_PACKET_SIZE => SizeType::MultiFrame,
            _ => unreachable!(),
        }
    }

    pub fn pop(&mut self) -> Option<CanDudeFrame> {
        (!self.completed()).then_some(())?;

        match self.size_type() {
            SizeType::SingleFrame => {
                let result = CanDudeFrame {
                    address: self.address,
                    data: arrayvec::ArrayVec::try_from(self.data).ok()?,
                    counter: self.data.len() as u8,
                    end_of_packet: true,
                };

                self.sent_counter = result.data.len();

                Some(result)
            }
            SizeType::MultiFrame => {
                let mut data =
                    arrayvec::ArrayVec::try_from(&self.data[{
                        let begin_index = self.sent_counter.min(self.data.len());
                        let end_index = (self.sent_counter + MAX_FRAME_SIZE).min(self.data.len());
                        begin_index..end_index
                    }]).ok()?;

                self.sent_counter += data.len();

                // append crc
                while !data.is_full() && self.sent_counter < self.data.len() + self.crc.len() {
                    data.push( self.crc[self.sent_counter-self.data.len()]);
                    self.sent_counter += 1;
                }

                let mut end_of_packet = self.sent_counter == self.data.len() + self.crc.len();

                Some(CanDudeFrame {
                    address: self.address,
                    data,
                    counter: self.sent_counter as u8,
                    end_of_packet,
                })
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CanDudePacketReceiverState {
    Empty,
    Receiving,
    Received(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanDudePacketReceiver<const CAPACITY: usize> {
    address: u8,
    data: [u8; CAPACITY],
    state: CanDudePacketReceiverState,
    received_frame: u16,
    first_frame_with_end: (usize, usize),   // frame number and received size
}

impl<const CAPACITY: usize> CanDudePacketReceiver<CAPACITY> {
    pub fn new(address: u8) -> CanDudePacketReceiver<CAPACITY> {
        Self {
            address,
            data: [0; CAPACITY],
            state: CanDudePacketReceiverState::Empty,
            received_frame: 0,
            first_frame_with_end: (0, 0),
        }
    }

    pub fn address(&self) -> u8 {
        self.address
    }
    pub fn state(&self) -> &CanDudePacketReceiverState {
        &self.state
    }

    pub fn data(&self) -> Option<&[u8]> {
        match self.state {
            CanDudePacketReceiverState::Received(len) => Some(self.data[..len].as_ref()),
            _ => None,
        }
    }

    pub fn reset(&mut self) {
        self.data.fill(0);
        self.state = CanDudePacketReceiverState::Empty;
        self.received_frame = 0;
        self.first_frame_with_end = (0, 0);
    }

    pub fn push(&mut self, frame: CanDudeFrame) {
        if self.address != frame.address || frame.counter as usize > MAX_PACKET_SIZE + 2 {
            return;
        }

        match &self.state {
            CanDudePacketReceiverState::Received(_) => return,
            _ => {
                // if single frames
                if frame.end_of_packet && frame.counter as usize == frame.data.len() {
                    self.data[0..frame.data.len()].clone_from_slice(frame.data.as_slice());
                    self.state = CanDudePacketReceiverState::Received(frame.data.len());
                }
                else {
                    /// Get range.
                    /// First is number of frame (all frames except last with MAX_FRAME_SIZE)
                    let frame_number = ((frame.counter as usize / MAX_FRAME_SIZE) * MAX_FRAME_SIZE) - MAX_FRAME_SIZE;
                    self.data[frame_number .. frame.counter as usize].clone_from_slice(frame.data.as_slice());

                    // mark frame is received
                    self.received_frame.set_bit(frame_number, true);
                    /// If there isn't frame with less pos
                    if self.first_frame_with_end.1 == 0 || self.first_frame_with_end.0 >= frame_number {
                        self.first_frame_with_end.0 = frame_number;
                        self.first_frame_with_end.1 = frame.counter as usize;
                    }

                    for pos in 0..(CAPACITY/MAX_FRAME_SIZE + (((CAPACITY % MAX_FRAME_SIZE) != 0) as usize)) {
                        match self.received_frame.bit(pos) {
                            false => break,
                            true => if self.first_frame_with_end.0 == pos {
                                // All frames before marked as received
                                let data = &self.data[0..self.first_frame_with_end.1];

                                break;
                            }
                        }

                    }

                }

            }
        }
/*
        let process = || -> Option<()> {
            // check sequential_is_valid
            match &self.state {
                CanDudePacketReceiverState::Received => return Some(()),
                CanDudePacketReceiverState::Receiving(counter) => {
                    match counter {
                        Counter::Bytes(current_len) => match &frame.counter {
                            Counter::Bytes(len) => (*current_len + 1
                                ..=*current_len + MAX_FRAME_SIZE as u8)
                                .contains(len)
                                .then_some(())?,
                            Counter::Frames(_) => return None,
                        },
                        // Ensure this is next frame
                        Counter::Frames(current_count) => match &frame.counter {
                            Counter::Bytes(_) => return None,
                            Counter::Frames(count) => {
                                (*count == current_count + 1).then_some(())?;
                            }
                        },
                    }
                }
                _ => {}
            };

            match &frame.counter {
                Counter::Bytes(bytes) => {
                    self.state = CanDudePacketReceiverState::Receiving(Counter::Bytes(*bytes));
                    (self.data.len() + frame.data.len() == *bytes as usize).then_some(())?;

                    match frame.end_of_packet {
                        false => self.data.extend(frame.data),
                        true => {
                            match self.data.len() {
                                // If this is first packet and it is last (single frame)
                                // Then just store all data
                                0 => self.data.extend(frame.data),
                                // Else extend data then check CRC
                                _ => {
                                    let (data, crc) = frame.data.split_at(frame.data.len() - 2);
                                    self.data.try_extend_from_slice(data).ok()?;
                                    let c = CRC.checksum(self.data.as_slice()).to_be_bytes();
                                    (c == crc).then_some(())?;
                                }
                            }

                            self.state = CanDudePacketReceiverState::Received;
                        }
                    }
                }
            }

            Some(())
        };

        match process() {
            Some(_) => {}
            None => self.reset(),
        };*/
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ttt() {
        let mut d = [0u8; 200]; // Initialize all 200 elements with 0
        d[0] = 1; // Set the first element
        d[1] = 23; // Set the second element
                   //let ss = CanDudePacket::new(&d);
    }

    #[test]
    fn can_dude_packet_read() {
        fn check(data: std::vec::Vec<u8>) {
            let mut p = CanDudePacketSender::new(12, &data).unwrap();

            let mut rec = CanDudePacketReceiver::<126>::new(12);
            while !matches!(rec.state, CanDudePacketReceiverState::Received(_)) {
                rec.push(p.pop().unwrap());
            }
            let rec_data = rec.data().unwrap();
            assert_eq!(rec_data.len(), data.len());
            assert_eq!(rec_data, data.as_slice());
        }

        for size in 11..=11_u16 {
            let mut data: std::vec::Vec<u8> = std::vec::Vec::with_capacity(size as usize);
            for i in 0..size {
                data.push(i as u8);
            }
            check(data);
        }
    }

    #[test]
    fn can_dude_packet_sender() {
        fn check(data: &[u8]) {
            let mut p = CanDudePacketSender::new(12, &data).unwrap();
            match data.len() {
                0..=10 => assert_eq!(p.size_type(), SizeType::SingleFrame),
                11..=126 => assert_eq!(p.size_type(), SizeType::MultiFrame),
                _ => unreachable!(),
            };

            match p.size_type() {
                SizeType::SingleFrame => {
                    assert_eq!(
                        p.pop(),
                        Some(CanDudeFrame {
                            address: 12,
                            data: arrayvec::ArrayVec::try_from(data).unwrap(),
                            counter: data.len() as u8,
                            end_of_packet: true,
                        })
                    );
                    assert_eq!(p.pop(), None);
                }
                SizeType::MultiFrame => {
                    let mut res_data: std::vec::Vec<u8> = std::vec::Vec::new();

                    let mut end_of_packet = false;
                    while let Some(frame) = p.pop() {
                        assert!(!end_of_packet);

                        assert_eq!(frame.address, 12);
                        res_data.extend(frame.data);
                        assert_eq!(frame.counter, res_data.len() as u8);

                        if frame.end_of_packet {
                            end_of_packet = true;
                            assert_eq!(p.pop(), None);
                        }
                    }

                    assert_eq!(res_data.len() - 2, data.len());

                    let d = &res_data[..res_data.len() - 2];
                    let c = &res_data[res_data.len() - 2..];
                    let crc: [u8; 2] = CRC.checksum(d).to_be_bytes();
                    assert_eq!(d, data);
                    assert_eq!(c, crc);

                    assert_eq!(p.pop(), None);
                }
            }
        }

        assert_eq!(CanDudePacketSender::new(12, &[]), None);

        for size in 1..=126_u16 {
            let mut data: std::vec::Vec<u8> = std::vec::Vec::with_capacity(size as usize);
            for i in 0..size {
                data.push(i as u8);
            }
            check(&data);
        }
    }

    #[test]
    fn from_to_canbus() {
        let id: u32 = 25 |  // address
            50 << 6 |       // count
            100 << 13 |     // byte 1
            200 << (13+8);  // byte 2
        let data: [u8; 3] = [1, 2, 3];

        let result = CanDudeFrame::from_canbus(id, data.as_ref()).unwrap();
        assert_eq!(result.address, 25);
        assert_eq!(result.end_of_packet, false);
        assert_eq!(result.counter, 50);
        assert_eq!(result.data[0], 100);
        assert_eq!(result.data[1], 200);
        assert_eq!(result.data[2], 1);
        assert_eq!(result.data[3], 2);
        assert_eq!(result.data[4], 3);

        let result = result.to_canbus();
        assert_eq!(result.0 & 0b11111, 25);
        assert_eq!(result.0 >> 5 & 0b1, 0);
        assert_eq!(result.0 >> 6 & 0b111_1111, 50);
        assert_eq!(result.0 >> 13 & 0xFF, 100);
        assert_eq!(result.0 >> (13 + 8) & 0xFF, 200);
        assert_eq!(result.1[0], 1);
        assert_eq!(result.1[1], 2);
        assert_eq!(result.1[2], 3);

        let id: u32 = 5 |        // address
            63 << 6 |       // count
            10 << 13 |      // byte 1
            20 << (13+8);   // byte 2
        let data: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

        let result = CanDudeFrame::from_canbus(id, data.as_ref()).unwrap();
        assert_eq!(result.address, 5);
        assert!(!result.end_of_packet);
        assert_eq!(result.counter,63);
        assert_eq!(result.data[0], 10);
        assert_eq!(result.data[1], 20);
        assert_eq!(result.data[2], 1);
        assert_eq!(result.data[3], 2);
        assert_eq!(result.data[4], 3);
        assert_eq!(result.data[5], 4);
        assert_eq!(result.data[6], 5);
        assert_eq!(result.data[7], 6);
        assert_eq!(result.data[8], 7);
        assert_eq!(result.data[9], 8);

        let result = result.to_canbus();
        assert_eq!(result.0 & 0b11111, 5);
        assert_eq!(result.0 >> 5 & 0b1, 0);
        assert_eq!(result.0 >> 6 & 0b1111111, 63);
        assert_eq!(result.0 >> 13 & 0xFF, 10);
        assert_eq!(result.0 >> (13 + 8) & 0xFF, 20);
        assert_eq!(result.1[0], 1);
        assert_eq!(result.1[1], 2);
        assert_eq!(result.1[2], 3);
        assert_eq!(result.1[3], 4);
        assert_eq!(result.1[4], 5);
        assert_eq!(result.1[5], 6);
        assert_eq!(result.1[6], 7);
        assert_eq!(result.1[7], 8);
    }
}
