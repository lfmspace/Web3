// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

import {Test, console} from "forge-std/Test.sol";

library SigUtils {
    // keccak256("Permit(address owner,address to,uint256 value,uint256 nonce,uint256 deadline,bytes32 msgHash)");
    bytes32 public constant PERMIT_TYPEHASH = 0x4ac553a37e01ec3c6bb3b436f31aa8101ceee19dbda551b523761ad60bad5146;

    struct Permit {
        address owner;
        address to;
        uint256 value;
        uint256 nonce;
        uint256 deadline;
        bytes32 msgHash;
    }

    // computes the hash of a permit
    function getStructHash(Permit memory _permit) internal pure returns (bytes32) {
        return keccak256(abi.encode(PERMIT_TYPEHASH, _permit.owner, _permit.to, _permit.value, _permit.nonce, _permit.deadline, _permit.msgHash));
    }

    // computes the hash of the fully encoded EIP-712 message for the domain, which can be used to recover the signer
    function getTypedDataHash(Permit memory _permit, bytes32 domainOperator) public pure returns (bytes32) {
        //console.log("test structHash is", uint256(getStructHash(_permit)));
        return keccak256(abi.encodePacked("\x19\x01", domainOperator, getStructHash(_permit)));
    }
}
