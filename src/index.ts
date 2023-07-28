import { RoomI } from 'discreetly-interfaces';
import genProof from './prover';
import { Identity } from '@semaphore-protocol/identity';

const room: RoomI = {
  id: '123',
  name: 'test',
  roomId: BigInt(7823578923898923898923),
  membership: {
    identityCommitments: [BigInt(123), BigInt(456)]
  }
};

const message = 'hello world';

const identity = new Identity();

console.log(genProof(room, message, identity));
