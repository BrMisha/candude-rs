#![cfg_attr(not(test), no_std)]

pub const MAX_FRAME_SIZE: usize = 10;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Counter {
    Bytes(u8),
    Frames(u8),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanDudeframe {
    pub address: u8,
    pub data: arrayvec::ArrayVec<u8, MAX_FRAME_SIZE>,
    pub counter: Counter,
    pub end_of_packet: bool,
}

impl CanDudeframe {
    pub fn from_canbus(id: u32, data: &[u8]) -> Option<Self> {
        let address = id as u8 & 0b11_111;
        let end_of_packet = ((id >> 5) as u8 & 0b1) == 1;

        let counter = (id >> 7) as u8 & 0b111_111;
        let counter= match (id >> 6) as u8 & 0b1 {
            0 => Counter::Bytes(counter),
            _ => Counter::Frames(counter),
        };

        let mut arr: arrayvec::ArrayVec<u8, MAX_FRAME_SIZE> = arrayvec::ArrayVec::new();
        arr.push((id >> 13) as u8);
        arr.push((id >> (13+8)) as u8);
        arr.try_extend_from_slice(data).ok()?;

        Some(Self {
            address,
            data: arr,
            counter,
            end_of_packet
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
            },
        }

        let mut iter = self.data.iter();
        if let Some(v) = iter.next() {
            id |= (*v as u32) << 13;
        }
        if let Some(v) = iter.next() {
            id |= (*v as u32) << 13+8;
        }

        let data = iter.as_slice();

        (id, data)
    }
}

enum SizeType {
    SingleFrame,
    Medium,
    Large,
}

pub struct CanDudePacket<'a> {
    pub data: &'a [u8],
    pub sent_counter: u16,
}

impl<'a> CanDudePacket<'a>
{
    pub fn new<'b: 'a, T>(data: &'b T) -> Self where T: AsRef<[u8]> {
        let data = data.as_ref();
        Self { data, sent_counter: 0 }
    }

    pub fn size_type(&self) -> SizeType {
        match self.data.len() {
            ..  11 => SizeType::SingleFrame,
            ..  63 => SizeType::Medium,
            ..  637 => SizeType::Large,
            _ => unreachable!()
        }
    }

    pub fn pop(&mut self) -> Option<CanDudeframe> {
        if self.sent_counter == 0 {
            
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ttt() {
        let mut d = [0u8; 200]; // Initialize all 200 elements with 0
        d[0] = 1;               // Set the first element
        d[1] = 23;              // Set the second element
        let ss = CanDudePacket::new(&d);
    }

    #[test]
    fn from_to_canbus() {
        let id: u32 = 25 |  // address
            1 << 5 |        // end of packet
            0 << 6 |        // counter in bytes
            50 << 7 |       // count
            100 << 13 |     // byte 1
            200 << 13+8;    // byte 2
        let data: [u8; 3] = [1,2,3];

        let result = CanDudeframe::from_canbus(id, data.as_ref()).unwrap();
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
        assert_eq!(result.0 >> 13+8 & 0xFF, 200);
        assert_eq!(result.1[0], 1);
        assert_eq!(result.1[1], 2);
        assert_eq!(result.1[2], 3);

        let id: u32 = 5 |   // address
            0 << 5 |        // end of packet
            1 << 6 |        // counter in frames
            63 << 7 |       // count
            10 << 13 |     // byte 1
            20 << 13+8;    // byte 2
        let data: [u8; 8] = [1,2,3,4,5,6,7,8];

        let result = CanDudeframe::from_canbus(id, data.as_ref()).unwrap();
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
        assert_eq!(result.0 >> 13+8 & 0xFF, 20);
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
