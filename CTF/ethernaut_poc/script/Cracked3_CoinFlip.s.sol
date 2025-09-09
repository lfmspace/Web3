// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.30;

import {Script, console} from "forge-std/Script.sol";
import {Cracked3_CoinFlip} from "../src/Cracked3_CoinFlip.sol";
interface ICoinFlip {
    function flip(bool _guess) external returns (bool);
    function consecutiveWins() external returns (uint256);
}
//forge script  --rpc-url sepolia --account metamask  script/Cracked3_CoinFlip.s.sol --broadcast
contract Cracked3_CoinFlipScript is Script {
    address ethernaut_contracts;
    Cracked3_CoinFlip coinFlip;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("CoinFlip_address"));
        //run2_10;
        coinFlip = Cracked3_CoinFlip(0x16E1A7c400310A63341c4a0BFcDe61d485688dA9);
    }
    // 运行10次
    function run() public {
        //run1();
        run2_10();
    }

    // 首次运行-部署合约
    function run1() public {
        vm.startBroadcast();
        coinFlip = new Cracked3_CoinFlip(ethernaut_contracts);
        uint256 oldWin = ICoinFlip(ethernaut_contracts).consecutiveWins();
        console.log("oldWin is", oldWin);
        bool success = coinFlip.guess();
        require(success, "guess fail");
        uint256 newWin = ICoinFlip(ethernaut_contracts).consecutiveWins();
        console.log("newWin is", newWin);
        require(oldWin + 1 == newWin, "fail");
        vm.stopBroadcast();
    }

    // 运行10次
    function run2_10() public {
        vm.startBroadcast();
        uint256 oldWin = ICoinFlip(ethernaut_contracts).consecutiveWins();
        console.log("oldWin is", oldWin);
        bool success = coinFlip.guess();
        require(success, "guess fail");
        uint256 newWin = ICoinFlip(ethernaut_contracts).consecutiveWins();
        console.log("newWin is", newWin);
        require(oldWin + 1 == newWin, "fail");
        vm.stopBroadcast();
    }
}
