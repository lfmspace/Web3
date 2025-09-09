// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked26_DoubleEntryPoint.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked26_DoubleEntryPointScript --broadcast
contract Cracked26_DoubleEntryPointScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("DoubleEntryPoint_address"));
    }

    //坎昆升级后自毁仅构造函数删代码，函数不删代码，ethernaut无法验证通过
    function run() public {
        vm.startBroadcast();
        address forta = address(IDoubleEntryPoint(ethernaut_contracts).forta());
        Cracked26_DetectionBot attack = new Cracked26_DetectionBot(forta, ethernaut_contracts);

        IForta(forta).setDetectionBot(address(attack));
        vm.stopBroadcast();
    }
}
