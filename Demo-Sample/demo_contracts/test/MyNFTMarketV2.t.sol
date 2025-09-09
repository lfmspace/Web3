// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from 'forge-std/Test.sol';
import {MyNFTMarketV2} from '../src/NFT/MyNFTMarketV2.sol';
import {MyNFT} from '../src/NFT/MyNFT.sol';
import {MyToken} from '../src/Token/MyToken.sol';
import {SigUtils2} from '../src/utils/SigUtils2.sol';
import {SigUtils3} from '../src/utils/SigUtils3.sol';
import '@openzeppelin/contracts/utils/Strings.sol';

contract MyNFTMarketV2Test is Test {
    // MyNFT public nft;
    // MyToken public token;
    // MyNFTMarketV2 public nftMarket;
    // address nftOwner;
    // address nftMarketOwner;
    // SigUtils2 public sigUtils;
    // SigUtils3 public sigUtils3;
    // uint256 ownerPrivateKey;
    // uint256 nftMarketOwnerPrivateKey;
    // function setUp() public {
    //     nftOwner = makeAddr('nftOwner');
    //     nft = new MyNFT(nftOwner);
    //     token = new MyToken();
    // }
    // function _testPermitList() public {
    //     nftMarketOwner = makeAddr('nftMarketOwner');
    //     nftMarket = new MyNFTMarketV2(address(nft), address(token));
    //     nftMarket.initialize(
    //         address(nft),
    //         address(token),
    //         address(nftMarketOwner),
    //         'MyNFTMarket',
    //         '1'
    //     );
    //     sigUtils = new SigUtils2(nft.DOMAIN_SEPARATOR());
    //     (address owner, uint256 pKey) = makeAddrAndKey('owner');
    //     ownerPrivateKey = pKey;
    //     address spender = address(nftMarket);
    //     vm.prank(nftOwner);
    //     uint256 tokenId = nft.mintNFT(
    //         owner,
    //         'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q'
    //     );
    //     SigUtils2.Permit memory permit = SigUtils2.Permit({
    //         owner: owner,
    //         to: spender,
    //         tokenId: tokenId,
    //         nonce: 0,
    //         deadline: 1 days
    //     });
    //     bytes32 digest = sigUtils.getTypedDataHash(permit);
    //     (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerPrivateKey, digest);
    //     vm.startPrank(owner);
    //     nftMarket.permitList(permit.tokenId, 100, permit.deadline, v, r, s);
    //     assertEq(nft.ownerOf(tokenId), address(nftMarket));
    //     vm.stopPrank();
    // }
    // function testPermitBuy() public {
    //     (address nftMarketOwner1, uint256 pmKey) = makeAddrAndKey(
    //         'nftMarketOwner'
    //     );
    //     nftMarketOwner = nftMarketOwner1;
    //     nftMarketOwnerPrivateKey = pmKey;
    //     nftMarket = new MyNFTMarketV2(address(nft), address(token));
    //     nftMarket.initialize(
    //         address(nft),
    //         address(token),
    //         address(nftMarketOwner),
    //         'MyNFTMarket',
    //         '1'
    //     );
    //     sigUtils3 = new SigUtils3(nftMarket.DOMAIN_SEPARATOR());
    //     address buyer = makeAddr('buyer');
    //     SigUtils3.Permit memory permit = SigUtils3.Permit({
    //         buyer: buyer,
    //         nonce: 0,
    //         deadline: 1 days
    //     });
    //     bytes32 digest = sigUtils3.getTypedDataHash(permit);
    //     (uint8 v, bytes32 r, bytes32 s) = vm.sign(pmKey, digest);
    //     //铸造一个nft给seller
    //     address seller = makeAddr('seller');
    //     vm.prank(nftOwner);
    //     uint256 tokenId = nft.mintNFT(
    //         seller,
    //         'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q'
    //     );
    //     //seller上架
    //     vm.startPrank(seller);
    //     nft.approve(address(nftMarket), tokenId);
    //     nftMarket.listUp(tokenId, 5);
    //     vm.stopPrank();
    //     vm.startPrank(buyer);
    //     //buyer申请金额并转入market
    //     token.applyToken(buyer);
    //     token.send(address(nftMarket), 6);
    //     nftMarket.permitBuy(tokenId, permit.deadline, v, r, s);
    //     assertEq(nft.ownerOf(tokenId), buyer);
    //     vm.stopPrank();
    // }
}
