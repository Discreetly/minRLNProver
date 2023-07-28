import { RLNProver } from 'rlnjs';
import { Group } from '@semaphore-protocol/group';
import { str2BigInt } from 'discreetly-interfaces';
import { poseidon1 } from 'poseidon-lite/poseidon1';
import { poseidon2 } from 'poseidon-lite/poseidon2';
import type { Identity } from '@semaphore-protocol/identity';
import type { MessageI, RoomI } from 'discreetly-interfaces';
import type { RLNFullProof, MerkleProof } from 'rlnjs';

function getMessageHash(message: string) {
  return poseidon1([str2BigInt(message)]);
}

function getRateCommitmentHash(identityCommitment: bigint, userMessageLimit: number | bigint) {
  return poseidon2([identityCommitment, userMessageLimit]);
}

const wasmPath = './rln/circuit.wasm';
const zkeyPath = './rln/final.zkey';
const prover: RLNProver = new RLNProver(wasmPath, zkeyPath);

interface proofInputsI {
  rlnIdentifier: bigint;
  identitySecret: bigint;
  userMessageLimit: bigint;
  messageId: bigint;
  merkleProof: MerkleProof;
  x: bigint;
  epoch: bigint;
}

async function genProof(
  room: RoomI,
  message: string,
  identity: Identity,
  messageId: bigint | number = 0,
  messageLimit: bigint | number = 1
): Promise<MessageI> {
  console.log(room, message, identity);
  const RLN_IDENIFIER = BigInt(room.id);
  const userMessageLimit = BigInt(messageLimit);
  const messageHash: bigint = getMessageHash(message);
  const group = new Group(RLN_IDENIFIER, 20, room.membership?.identityCommitments);
  const rateCommitment: bigint = getRateCommitmentHash(identity.getCommitment(), userMessageLimit);
  const proofInputs: proofInputsI = {
    rlnIdentifier: RLN_IDENIFIER,
    identitySecret: identity.getSecret(),
    userMessageLimit: userMessageLimit,
    messageId: BigInt(messageId),
    merkleProof: group.generateMerkleProof(group.indexOf(rateCommitment)),
    x: messageHash,
    epoch: BigInt(Date.now().toString())
  };
  //console.debug('PROOFINPUTS:', proofInputs);
  return prover.generateProof(proofInputs).then((proof: RLNFullProof) => {
    console.log('Proof generated!');
    const msg: MessageI = {
      id: proof.snarkProof.publicSignals.nullifier.toString(),
      message: message,
      roomId: RLN_IDENIFIER,
      proof
    };
    return msg;
  });
}

export default genProof;
