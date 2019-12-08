# FM-Net v2

A node is a 256 bit word
A net is an array of nodes

A Node has the following binary format

| Name        | Size | Bits    | Description             |
|-------------|------|---------|-------------------------|
| free        | 1    | 0       | Node is a free variable |
| node type   | 1    | 1       | CON or DUP              |
| primarySlot | 2    | 2:3     | Primary slot points to  |
| leftSlot    | 2    | 4:5     | Left slot points to     |
| rightSlot   | 2    | 6:7     | Right slot points to    |
| meta        | 56   | 8:63    | reserved for future use |
| primary     | 64   | 64:127  | primary slot            |
| left        | 64   | 128:191 | left slot               |
| right       | 64   | 192:255 | right slot              |


Node Slots can be one of the following:

| Name | Code | Description |
|------|------|-------------|
| P    | 00  | to Primary  |
| L    | 01  | to Left     |
| R    | 10  | to Right    |
