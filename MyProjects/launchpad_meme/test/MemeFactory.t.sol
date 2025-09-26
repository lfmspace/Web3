// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import "../src/Meme/Meme.sol";
import "../src/Meme/MemeFactory.sol";

contract MemeFactoryTest is Test {
    Meme public meme;
    MemeFactory public factory;
    address public uniswapV2Factory;
    address public uniswapV2Router;
    uint256 public constant cure_param_a = 31015527287;
    uint256 public constant cure_param_b = 1586163595;

    function setUp() public {
        uniswapV2Factory = vm.parseAddress(vm.envString("UNISWAP_FACTORY_SEPOLIA"));
        uniswapV2Router = vm.parseAddress(vm.envString("UNISWAP_ROUTER_SEPOLIA"));
        meme = new Meme();
        factory = new MemeFactory(address(meme), uniswapV2Router, uniswapV2Factory, cure_param_a, cure_param_b);
    }

    function testCreateToken_Success() public {
        address proxy = factory.createToken("TestMeme", "TM");
        assert(factory.tokenStates(proxy) == MemeFactory.TokenState.FUNDING);
    }
}
