// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

interface IVault {
    function unlock(bytes32 _password) external;
}
// let contractAddress = '';
// const password = await web3.eth.getStorageAt(contractAddress, '0');
// console.log('Current password # is ', password);
//forge script  --rpc-url sepolia --account metamask  Cracked8_VaultScript --broadcast
contract Cracked8_VaultScript is Script {
    address ethernaut_contracts;
    bytes32 password;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Vault_address"));
        //password=;
    }

    function run() public {
        vm.startBroadcast();
        IVault(ethernaut_contracts).unlock(password);
        vm.stopBroadcast();
    }
}
