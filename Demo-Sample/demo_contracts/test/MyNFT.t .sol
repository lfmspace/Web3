// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from 'forge-std/Test.sol';
import {MyNFT} from '../src/NFT/MyNFT.sol';
import {SigUtils2} from '../src/utils/SigUtils2.sol';
import '@openzeppelin/contracts/utils/Strings.sol';

contract MyNFTTest is Test {
    MyNFT public nft;
    address nftOwner;
    SigUtils2 public sigUtils;
    uint256 ownerPrivateKey;

    function setUp() public {
        nftOwner = makeAddr('nftOwner');
        nft = new MyNFT(nftOwner);
        sigUtils = new SigUtils2(nft.DOMAIN_SEPARATOR());
    }

    function testPermit() public {
        (address owner, uint256 pKey) = makeAddrAndKey('owner');
        ownerPrivateKey = pKey;
        address spender = makeAddr('spender');

        vm.prank(nftOwner);
        uint256 tokenId = nft.mintNFT(
            owner,
            'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q'
        );
        SigUtils2.Permit memory permit = SigUtils2.Permit({
            owner: owner,
            to: spender,
            tokenId: tokenId,
            nonce: 0,
            deadline: 1 days
        });

        bytes32 digest = sigUtils.getTypedDataHash(permit);

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ownerPrivateKey, digest);

        vm.startPrank(owner);
        nft.permit(
            permit.owner,
            permit.to,
            permit.tokenId,
            permit.deadline,
            v,
            r,
            s
        );
        assertEq(nft.getApproved(permit.tokenId), spender);
        vm.stopPrank();
    }
}
