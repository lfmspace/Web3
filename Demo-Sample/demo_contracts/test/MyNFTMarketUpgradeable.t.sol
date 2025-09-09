// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from 'forge-std/Test.sol';
import {MyNFTMarketV2} from '../src/NFT/MyNFTMarketV2.sol';
import {MyNFTMarketV1} from '../src/NFT/MyNFTMarketV1.sol';
import '@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol';
import '@openzeppelin/contracts/proxy/ERC1967/ERC1967Utils.sol';
import {MyNFT} from '../src/NFT/MyNFT.sol';
import {MyToken} from '../src/Token/MyToken.sol';

import '../src/utils/StringUtils.sol';

contract MyNFTMarketUpgradeableTest is Test {
    MyNFTMarketV2 public nftMarketV2;
    MyNFTMarketV1 public nftMarketV1;
    ERC1967Proxy proxy;
    address owner;
    address nftOwner;
    MyNFT nft;
    MyToken token;

    function setUp() public {
        owner = makeAddr('0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC'); //管理员
        nftOwner = makeAddr('nftOwner');
        nft = new MyNFT(nftOwner);
        token = new MyToken();
        nftMarketV1 = new MyNFTMarketV1();

        vm.prank(owner);
        proxy = new ERC1967Proxy(
            address(nftMarketV1),
            abi.encodeCall(
                nftMarketV1.initialize,
                (address(nft), address(token), address(owner))
            )
        );
    }

    function _testMarketV1Func() public {
        vm.startPrank(nftOwner);
        uint256 tokenId = nft.mintNFT(
            owner,
            'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q'
        );
        vm.stopPrank();
        console.log('proxy address', address(proxy));
        vm.startPrank(owner);
        nft.approve(address(proxy), tokenId);
        console.log('nft owner pre address', nft.ownerOf(tokenId));

        (bool s, ) = address(proxy).call(
            abi.encodeWithSignature('listUp(uint256,uint256)', tokenId, 100)
        );
        vm.stopPrank();
        assertEq(nft.ownerOf(tokenId), address(proxy));
    }

    function _testMarketV1NoV2Func() public {
        vm.expectRevert();
        (bool s, ) = address(proxy).call(abi.encodeWithSignature('getCount()'));
    }

    function testUpgradeable() public {
        (, bytes memory cname1) = address(proxy).call(
            abi.encodeWithSignature('setcname()')
        );
        console.log(
            'v1-cname is',
            abi.decode(abi.encodePacked(cname1), (uint256))
        );

        nftMarketV2 = new MyNFTMarketV2(address(nft), address(token));

        vm.prank(owner);
        // MyNFTMarketV1(address(proxy)).upgradeToAndCall(
        //     address(nftMarketV2),
        //     abi.encodeCall(nftMarketV2.initialize, ('MyNFTMarket', '1'))
        // );

        (bool usuccess, bytes memory up) = address(proxy).call(
            abi.encodeCall(
                nftMarketV1.upgradeToAndCall,
                (
                    address(nftMarketV2),
                    abi.encodeCall(nftMarketV2.initialize, ('MyNFTMarket', '1'))
                )
            )
        );
        if (!usuccess) {
            revert('wewewq');
        }

        (, bytes memory cname2) = address(proxy).call(
            abi.encodeWithSignature('getcname()')
        );
        console.log(
            'v2-cname is',
            abi.decode(abi.encodePacked(cname2), (uint256))
        );
        // console.log(
        //     'nft is',
        //     abi.decode(
        //         abi.encodePacked(bytes32(uint256(uint160(address(nft))))),
        //         (uint256)
        //     )
        // );
    }
}
