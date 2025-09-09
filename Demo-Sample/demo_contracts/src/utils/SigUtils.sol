// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

import {Test, console} from 'forge-std/Test.sol';

contract SigUtils {
    bytes32 internal DOMAIN_SEPARATOR;

    constructor(bytes32 _DOMAIN_SEPARATOR) {
        DOMAIN_SEPARATOR = _DOMAIN_SEPARATOR;
    }

    // keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");
    bytes32 public constant PERMIT_TYPEHASH =
        0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9;

    struct Permit {
        address owner;
        address spender;
        uint256 value;
        uint256 nonce;
        uint256 deadline;
    }

    // computes the hash of a permit
    function getStructHash(
        Permit memory _permit
    ) internal pure returns (bytes32) {
        return
            keccak256(
                abi.encode(
                    PERMIT_TYPEHASH,
                    _permit.owner,
                    _permit.spender,
                    _permit.value,
                    _permit.nonce,
                    _permit.deadline
                )
            );
    }

    // computes the hash of the fully encoded EIP-712 message for the domain, which can be used to recover the signer
    function getTypedDataHash(
        Permit memory _permit
    ) public view returns (bytes32) {
        return
            keccak256(
                abi.encodePacked(
                    '\x19\x01',
                    DOMAIN_SEPARATOR,
                    getStructHash(_permit)
                )
            );
    }

    bytes16 private constant _HEX_SYMBOLS = '0123456789abcdef';
    function toHexString(bytes32 data) public pure returns (string memory) {
        bytes memory str = new bytes(64); // bytes32是32字节，每字节2个16进制字符
        for (uint256 i = 0; i < 32; i++) {
            uint8 byteValue = uint8(data[i]);
            str[2 * i] = _HEX_SYMBOLS[byteValue >> 4]; // 高4位
            str[2 * i + 1] = _HEX_SYMBOLS[byteValue & 0x0f]; // 低4位
        }
        return string(str);
    }
}
