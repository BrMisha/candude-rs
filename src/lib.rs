#![cfg_attr(not(test), no_std)]

pub const MAX_FRAME_SIZE: usize = 10;
const X25: crc::Crc<u16> = crc::Crc::<u16>::new(&crc::CRC_16_IBM_SDLC);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Counter {
    Bytes(u8),
    Frames(u8),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanDudeFrame {
    pub address: u8,
    pub data: arrayvec::ArrayVec<u8, MAX_FRAME_SIZE>,
    pub counter: Counter,
    pub end_of_packet: bool,
}

impl CanDudeFrame {
    pub fn from_canbus(id: u32, data: &[u8]) -> Option<Self> {
        let address = id as u8 & 0b11_111;
        let end_of_packet = ((id >> 5) as u8 & 0b1) == 1;

        let counter = (id >> 7) as u8 & 0b111_111;
        let counter = match (id >> 6) as u8 & 0b1 {
            0 => Counter::Bytes(counter),
            _ => Counter::Frames(counter),
        };

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
        match self.counter {
            Counter::Bytes(c) => id |= (c as u32 & 0b111111) << 7,
            Counter::Frames(c) => {
                id |= 1 << 6;
                id |= (c as u32 & 0b111111) << 7;
            }
        }

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
    Medium,
    Large,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanDudePacketSender<'a> {
    pub address: u8,
    pub data: &'a [u8],
    pub sent_counter: usize, // with len and crc
}

impl<'a> CanDudePacketSender<'a> {
    pub fn new<'b: 'a, T>(address: u8, data: &'b T) -> Option<Self>
    where
        T: AsRef<[u8]>,
    {
        let data = data.as_ref();
        (!data.is_empty()).then_some(())?;

        Some(Self {
            address,
            data,
            sent_counter: 0,
        })
    }

    pub fn size_type(&self) -> SizeType {
        match self.data.len() {
            0..=10 => SizeType::SingleFrame,
            11..=62 => SizeType::Medium,
            63..=636 => SizeType::Large,
            _ => unreachable!(),
        }
    }

    pub fn pop(&mut self) -> Option<CanDudeFrame> {
        match self.size_type() {
            SizeType::SingleFrame => {
                (self.sent_counter < self.data.len()).then_some(())?;

                let result = CanDudeFrame {
                    address: self.address,
                    data: arrayvec::ArrayVec::try_from(self.data).ok()?,
                    counter: Counter::Bytes(self.data.len() as u8),
                    end_of_packet: true,
                };

                self.sent_counter = result.data.len();

                Some(result)
            }
            SizeType::Medium => {
                (self.sent_counter < self.data.len() + 2).then_some(())?;

                let end_index = (self.sent_counter + MAX_FRAME_SIZE).min(self.data.len());
                let mut data =
                    arrayvec::ArrayVec::try_from(&self.data[self.sent_counter..end_index]).ok()?;

                self.sent_counter += data.len();
                let mut end_of_packet = false;

                if data.capacity() - data.len() >= 2 {
                    let crc: [u8; 2] = X25.checksum(self.data).to_be_bytes();
                    data.extend(crc);
                    self.sent_counter += crc.len();
                    end_of_packet = true;
                }

                Some(CanDudeFrame {
                    address: self.address,
                    data,
                    counter: Counter::Bytes(self.sent_counter as u8),
                    end_of_packet,
                })
            }
            SizeType::Large => {
                (self.sent_counter < self.data.len() + 4).then_some(())?;

                let mut data = match self.sent_counter {
                    0 => {
                        let mut data = arrayvec::ArrayVec::new();
                        let len: [u8; 2] = (self.data.len() as u16).to_be_bytes();
                        data.extend(len);
                        self.sent_counter += len.len();

                        while data.len() < data.capacity() {
                            data.push(self.data[self.sent_counter - 2]);
                            self.sent_counter += 1;
                        }

                        data
                    }
                    _ => {
                        let end_index =
                            (self.sent_counter - 2 + MAX_FRAME_SIZE).min(self.data.len());
                        let data = arrayvec::ArrayVec::try_from(
                            &self.data[self.sent_counter - 2..end_index],
                        )
                            .ok()?;

                        self.sent_counter += data.len();
                        data
                    }
                };

                let mut end_of_packet = false;

                if data.capacity() - data.len() >= 2 {
                    let crc: [u8; 2] = X25.checksum(self.data).to_be_bytes();
                    data.extend(crc);
                    self.sent_counter += crc.len();
                    end_of_packet = true;
                }

                Some(CanDudeFrame {
                    address: self.address,
                    data,
                    counter: Counter::Frames(((self.sent_counter + 9) / MAX_FRAME_SIZE) as u8),
                    end_of_packet,
                })
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CanDudePacketReceiverState {
    Empty,
    Receiving(Counter),
    Received,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanDudePacketReceiver<const CAPACITY: usize> {
    pub address: u8,
    pub data: arrayvec::ArrayVec<u8, CAPACITY>,
    //pub received_counter: usize, // with len and crc
    pub state: CanDudePacketReceiverState,
    pub received_len: u16,  // for large
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CanDudePacketReceiverError {
    Sequential,

}

impl<const CAPACITY: usize> CanDudePacketReceiver<CAPACITY> {
    pub fn new(address: u8) -> CanDudePacketReceiver<CAPACITY> {
        Self {
            address,
            data: arrayvec::ArrayVec::new(),
            state: CanDudePacketReceiverState::Empty,
            received_len: 0,
        }
    }

    pub fn push(&mut self, frame: CanDudeFrame) {
        if self.address != frame.address { return; }

        let process = || -> Option<()> {
            // check sequential_is_valid
            match &self.state {
                CanDudePacketReceiverState::Received => return Some(()),
                CanDudePacketReceiverState::Receiving(counter) => {
                    match counter {
                        Counter::Bytes(current_len) => {
                            match &frame.counter {
                                Counter::Bytes(len) =>
                                    (*current_len+1..=*current_len + MAX_FRAME_SIZE as u8).contains(&len).then_some(())?
                                ,
                                Counter::Frames(_) => return None,
                            }
                        }
                        Counter::Frames(current_count) => {
                            match &frame.counter {
                                Counter::Bytes(_) => return None,
                                Counter::Frames(count) => {
                                    (*count == current_count+1).then_some(())?;
                                },
                            }
                        }
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
                                    let (data, crc) = frame.data.split_at(frame.data.len()-2);
                                    self.data.try_extend_from_slice(data).ok()?;
                                    let c = X25.checksum(self.data.as_slice()).to_be_bytes();
                                    (c == crc).then_some(())?;
                                }
                            }

                            self.state = CanDudePacketReceiverState::Received;
                        },
                    }
                }
                Counter::Frames(frames) => {
                    self.state = CanDudePacketReceiverState::Receiving(Counter::Frames(*frames));
                }
            }

            Some(())
        };



        match process() {
            Some(_) => {}
            None => {
                self.data = arrayvec::ArrayVec::new();
                self.state = CanDudePacketReceiverState::Empty;
            }
        };
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
        /*let data: &[u8] = &[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18];
        let mut p = CanDudePacket::new(12, &data).unwrap();

        let mut rec = CanDudePacketReceiver::<100>::new(12);
        rec.push(p.pop().unwrap());
        assert!(matches!(rec.state, CanDudePacketReceiverState::Receiving(_)));
        rec.push(p.pop().unwrap());
        assert_eq!(rec.state, CanDudePacketReceiverState::Received);
        assert_eq!(rec.data.as_slice(), data);
*/


        for size in 1..=62_u16 {
            let mut data: std::vec::Vec<u8> = std::vec::Vec::with_capacity(size as usize);
            for i in 0..size {
                data.push(i as u8);
            }
            let mut p = CanDudePacketSender::new(12, &data).unwrap();

            let mut rec = CanDudePacketReceiver::<1000>::new(12);

            while rec.state != CanDudePacketReceiverState::Received {
                rec.push(p.pop().unwrap());
            }

            assert_eq!(rec.data.as_slice(), data.as_slice());
        }
    }

    #[test]
    fn can_dude_packet_sender() {
        fn check(data: &[u8]) {
            let mut p = CanDudePacketSender::new(12, &data).unwrap();
            match data.len() {
                0..=10 => assert_eq!(p.size_type(), SizeType::SingleFrame),
                11..=62 => assert_eq!(p.size_type(), SizeType::Medium),
                63..=636 => assert_eq!(p.size_type(), SizeType::Large),
                _ => unreachable!(),
            };

            match p.size_type() {
                SizeType::SingleFrame => {
                    assert_eq!(
                        p.pop(),
                        Some(CanDudeFrame {
                            address: 12,
                            data: arrayvec::ArrayVec::try_from(data).unwrap(),
                            counter: Counter::Bytes(data.len() as u8),
                            end_of_packet: true,
                        })
                    );
                    assert_eq!(p.pop(), None);
                }
                SizeType::Medium => {
                    let mut res_data: std::vec::Vec<u8> = std::vec::Vec::new();

                    let mut end_of_packet = false;
                    while let Some(frame) = p.pop() {
                        assert_eq!(end_of_packet, false);

                        assert_eq!(frame.address, 12);
                        res_data.extend(frame.data);
                        assert_eq!(frame.counter, Counter::Bytes(res_data.len() as u8));

                        if frame.end_of_packet {
                            end_of_packet = true;
                            assert_eq!(p.pop(), None);
                        }
                    }

                    assert_eq!(res_data.len() - 2, data.len());

                    let d = &res_data[..res_data.len() - 2];
                    let c = &res_data[res_data.len() - 2..];
                    let crc: [u8; 2] = X25.checksum(d).to_be_bytes();
                    assert_eq!(d, data);
                    assert_eq!(c, crc);

                    assert_eq!(p.pop(), None);
                }
                SizeType::Large => {
                    let mut res_data: std::vec::Vec<u8> = std::vec::Vec::new();

                    let mut end_of_packet = false;
                    while let Some(frame) = p.pop() {
                        assert_eq!(end_of_packet, false);

                        assert_eq!(frame.address, 12);
                        res_data.extend(frame.data);
                        assert_eq!(
                            frame.counter,
                            Counter::Frames(((res_data.len() + 9) / MAX_FRAME_SIZE) as u8)
                        );

                        if frame.end_of_packet {
                            end_of_packet = true;
                            assert_eq!(p.pop(), None);
                        }
                    }

                    assert_eq!(res_data.len() - 4, data.len());

                    let len = u16::from_be_bytes(res_data[..2].try_into().unwrap());
                    let d = &res_data[2..res_data.len() - 2];
                    let c = &res_data[res_data.len() - 2..];
                    let crc: [u8; 2] = X25.checksum(d).to_be_bytes();
                    assert_eq!(len, data.len() as u16);
                    assert_eq!(d, data);
                    assert_eq!(c, crc);

                    assert_eq!(p.pop(), None);
                }
            }
        }

        assert_eq!(CanDudePacketSender::new(12, &[]), None);

        for size in 1..=636_u16 {
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
            1 << 5 |        // end of packet
            0 << 6 |        // counter in bytes
            50 << 7 |       // count
            100 << 13 |     // byte 1
            200 << 13+8; // byte 2
        let data: [u8; 3] = [1, 2, 3];

        let result = CanDudeFrame::from_canbus(id, data.as_ref()).unwrap();
        assert_eq!(result.address, 25);
        assert_eq!(result.end_of_packet, true);
        assert_eq!(result.counter, Counter::Bytes(50));
        assert_eq!(result.data[0], 100);
        assert_eq!(result.data[1], 200);
        assert_eq!(result.data[2], 1);
        assert_eq!(result.data[3], 2);
        assert_eq!(result.data[4], 3);

        let result = result.to_canbus();
        assert_eq!(result.0 & 0b11111, 25);
        assert_eq!(result.0 >> 5 & 0b1, 1);
        assert_eq!(result.0 >> 6 & 0b1, 0);
        assert_eq!(result.0 >> 7 & 0b111111, 50);
        assert_eq!(result.0 >> 13 & 0xFF, 100);
        assert_eq!(result.0 >> 13 + 8 & 0xFF, 200);
        assert_eq!(result.1[0], 1);
        assert_eq!(result.1[1], 2);
        assert_eq!(result.1[2], 3);

        let id: u32 = 5 |   // address
            0 << 5 |        // end of packet
            1 << 6 |        // counter in frames
            63 << 7 |       // count
            10 << 13 |     // byte 1
            20 << 13+8; // byte 2
        let data: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

        let result = CanDudeFrame::from_canbus(id, data.as_ref()).unwrap();
        assert_eq!(result.address, 5);
        assert_eq!(result.end_of_packet, false);
        assert_eq!(result.counter, Counter::Frames(63));
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
        assert_eq!(result.0 >> 6 & 0b1, 1);
        assert_eq!(result.0 >> 7 & 0b111111, 63);
        assert_eq!(result.0 >> 13 & 0xFF, 10);
        assert_eq!(result.0 >> 13 + 8 & 0xFF, 20);
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
