// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import {Bank} from "../src/Bank.sol";

contract BankTest is Test {
    Bank public bank;

    function setUp() public {
        bank = new Bank();
        //counter.setNumber(0);
    }

    function test_DepositMoney(uint32 x) public {
        address alice = makeAddr("alice");
        vm.prank(alice);
        deal(alice, 10 ether);
        bank.depositMoney{value: x}();
        assertEq(bank.getBalance(), x);
    }
}
