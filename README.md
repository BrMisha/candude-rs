# CAN-DUDE
## Higher-level over the CanBus 2.0B protocol.
### Features:
- Multi-master, multi-slave
- Request-answer
- Push (message from slave to master without request)
- 5 bit addressing (32 nodes)
- 10 bytes frame size
- Max packet size up to 636 bytes 

![can extended.png](can%20extended.png)
Extended ID has 29 bits, but the CAN-DUDE uses 6 bit for node addressing and 16 bites to extend data size. 
So maximal data size capacity in frame is 8+2 = 10 bytes.

## Protocol description
### Extended ID field (29 bits)

| 16 (2 bytes of data)  | 6 (counter)                               | 1 (counter type)                                                                 | 1 (end of packet)     | 5 (address)   |
|-----------------------|-------------------------------------------|----------------------------------------------------------------------------------|-----------------------|---------------|
| first 2 bytes of data | Count of sent (bytes or frames) of packet | 0 - Left 6 bites has counter of bytes<br/>1 - Left 6 bites has counter of frames | Flag of end of packet | Slave address | 
### Data field
One frame can contain up to 10 bytes of data. Part of data contains in the canbus address field.

| Byte number | Location                     |
|-------------|------------------------------|
| 0           | 11...19 bites of extended ID |
| 1           | 20...28 bites of extended ID |
| 2           | 0 byte of data field         |
| 3           | 1 byte of data field         |
| 4           | 2 byte of data field         |
| 5           | 3 byte of data field         |
| 6           | 4 byte of data field         |
| 7           | 5 byte of data field         |
| 8           | 6 byte of data field         |
| 9           | 7 byte of data field         |
### Packet structure
Packet may have 3 types:
1. Single framed. All packet contains in one frame (up to 10 bytes).
2. Up to 62 bytes. Bit `counter type` is 0, packet has 64 bytes where 2 bytes of CRC16 at and.
3. Up to 636 bytes. Bit `counter type` is 1, packet has 640 bytes where 2 bytes of len at begin and 2 bytes of CRC16 at and.