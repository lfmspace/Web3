// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from 'forge-std/Test.sol';
import '../src/Meme/Meme.sol';
import '../src/Meme/MemeFactory.sol';
import {SigUtils} from '../src/utils/SigUtils.sol';
import '@openzeppelin/contracts/utils/Strings.sol';

contract MemeTest is Test {
    Meme public meme;
    MemeFactory public factory;
    address os;

    function setUp() public {
        os = makeAddr('os');
        meme = new Meme(os);
        factory = new MemeFactory(address(meme), os);
    }

    function testMint() public {
        //meme发行者
        address memeOwner = makeAddr('memeOwner');
        vm.startPrank(memeOwner);
        uint256 perMint = 10;
        uint256 price = 1;
        address proxy = factory.deployMeme('MyMeme', 10000, perMint, price);
        address proxy2 = factory.deployMeme('MyMeme2', 10000, perMint, price);
        vm.stopPrank();

        address alice = makeAddr('alice');
        deal(alice, 100 ether);

        vm.startPrank(alice);

        bytes memory payload = abi.encodeWithSelector(Meme.mintMeme.selector);
        (bool success, ) = proxy.call{value: 10}(payload);
        console.log('meme is:', success);
        assert(success);
        assertEq(os.balance, (price * perMint * 1) / 100);
        assertEq(memeOwner.balance, (price * perMint * 99) / 100);
        vm.stopPrank();
    }
}
