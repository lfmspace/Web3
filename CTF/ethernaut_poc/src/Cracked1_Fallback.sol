// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Cracked1_Fallback {
    constructor(address _fallback) payable {
        require(msg.value < 0.001 ether);
        selfdestruct(payable(_fallback));
    }
}
