# CAN-DUDE
## Higher-level over the CanBus 2.0B protocol.
### Features:
- Multi-master, multi-slave
- Request-answer
- Push (message from slave to master without request)
- 5 bit addressing (32 nodes)
- 10 bytes frame size
- Max packet size up to 126 bytes
- Max packet size of single frame is 10 bytes

![can extended.png](can%20extended.png)
Extended ID has 29 bits, but the CAN-DUDE uses 6 bit for node addressing and 16 bites to extend data size. 
So maximal data size capacity in frame is 8+2 = 10 bytes.

## Protocol description
### Extended ID field (29 bits)

| 16 (2 bytes of data)  | 7 (counter)                   | 1 (end of packet)     | 5 (address)   |
|-----------------------|-------------------------------|-----------------------|---------------|
| first 2 bytes of data | Count of sent bytes of packet | Flag of end of packet | Slave address | 
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
Packet may have 2 types:
1. Single framed. All packet contains in one frame (up to 10 bytes).
2. Up to 126 bytes. Packet has 128 bytes where 2 last bytes of CRC16 at end.