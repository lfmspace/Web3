// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import {Test, console} from "forge-std/Test.sol";
import "../../src/NFTRent/RTNFT.sol";
import "../utils/SigUtils.sol";
import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import {SymTest} from "halmos-cheatcodes/SymTest.sol";

contract RTNFTTest is Test {
    RTNFT public nft;
    address nftOwner;
    address attacker;
    address tokenOwner;
    address tokenTo;
    uint256 tokenOwnerPrivateKey;
    uint256 attackerPrivateKey;
    uint256 defaultTokenId;

    error OwnableUnauthorizedAccount(address account);
    error ERC2612InvalidSigner(address signer, address owner);
    error ERC2612ExpiredSignature(uint256 deadline);
    event NFTChange(address from, address to, uint256 tokenId, string nftUrl);

    function setUp() public {
        nftOwner = makeAddr("nftOwner");
        nft = new RTNFT(nftOwner);
        (tokenOwner, tokenOwnerPrivateKey) = makeAddrAndKey("tokenOwner");
        (attacker, attackerPrivateKey) = makeAddrAndKey("attacker");
        tokenTo = makeAddr("tokenTo");

        vm.prank(nftOwner);
        defaultTokenId = nft.mintNFT(tokenOwner, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q");
    }
    /*****************************************************************单元测试-开始**********************************************************************/

    /**
     * 测试铸造NFT_合约所有者铸造
     */
    function testMintNFT() public {
        vm.prank(nftOwner);
        string memory url = "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q";
        uint256 tokenId = nft.mintNFT(tokenOwner, url);
        assertEq(nft.tokenURI(tokenId), url);
        assertEq(nft.ownerOf(tokenId), tokenOwner);
    }

    /**
     * 测试铸造NFT_非合约所有者铸造
     */
    function testMintNFT_NotOwner() public {
        string memory url = "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q";

        vm.expectRevert(abi.encodeWithSelector(OwnableUnauthorizedAccount.selector, attacker));
        vm.prank(attacker);
        uint256 tokenId = nft.mintNFT(tokenOwner, url);
    }

    /**
     * 测试Token授权_正常
     */
    function testPermit() public {
        SigUtils.Permit memory permit = SigUtils.Permit({owner: tokenOwner, to: tokenTo, value: defaultTokenId, nonce: nft.nonces(tokenOwner, uint192(defaultTokenId)), deadline: block.timestamp + 1 hours, msgHash: 0});
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(tokenOwnerPrivateKey, digest);

        vm.startPrank(tokenOwner);
        nft.permit(permit.owner, permit.to, permit.value, permit.deadline, 0, v, r, s);
        assertEq(nft.getApproved(permit.value), tokenTo);
        vm.stopPrank();
    }

    /**
     * 测试Token授权_攻击者使用攻击者私钥签名
     */
    function testPermit_UseAttackerSign() public {
        //使用攻击者签名授权不属于他的Token
        SigUtils.Permit memory permit = SigUtils.Permit({owner: tokenOwner, to: attacker, value: defaultTokenId, nonce: nft.nonces(tokenOwner, uint192(defaultTokenId)), deadline: block.timestamp + 1 hours, msgHash: 0});
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(attackerPrivateKey, digest);

        vm.expectRevert(abi.encodeWithSelector(ERC2612InvalidSigner.selector, attacker, tokenOwner));
        vm.prank(attacker);
        nft.permit(permit.owner, permit.to, permit.value, permit.deadline, 0, v, r, s);
    }

    /**
     * 测试Token授权_授权超时
     */
    function testPermit_Deadline() public {
        SigUtils.Permit memory permit = SigUtils.Permit({owner: tokenOwner, to: tokenTo, value: defaultTokenId, nonce: nft.nonces(tokenOwner, uint192(defaultTokenId)), deadline: block.timestamp - 1, msgHash: 0});
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(tokenOwnerPrivateKey, digest);

        vm.expectRevert(abi.encodeWithSelector(ERC2612ExpiredSignature.selector, permit.deadline));
        vm.prank(tokenOwner);
        nft.permit(permit.owner, permit.to, permit.value, permit.deadline, 0, v, r, s);
    }

    /**
     * 测试Token授权_篡改签名数据
     */
    function testPermit_ErrorData() public {
        //使用攻击者签名授权不属于他的Token
        SigUtils.Permit memory permit = SigUtils.Permit({owner: tokenOwner, to: attacker, value: defaultTokenId, nonce: nft.nonces(tokenOwner, uint192(defaultTokenId)), deadline: block.timestamp + 1 hours, msgHash: keccak256(abi.encode(1, 2, 3))});
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(tokenOwnerPrivateKey, digest);

        bytes32 errorMsgHash = keccak256(abi.encode(4, 5));
        address errorSigner = address(0);
        {
            //错误参数的哈希
            SigUtils.Permit memory permit2 = SigUtils.Permit({owner: tokenOwner, to: attacker, value: defaultTokenId, nonce: nft.nonces(tokenOwner, uint192(defaultTokenId)), deadline: block.timestamp + 1 hours, msgHash: errorMsgHash});
            bytes32 digest2 = SigUtils.getTypedDataHash(permit2, nft.DOMAIN_SEPARATOR());
            (uint8 v2, bytes32 r2, bytes32 s2) = vm.sign(tokenOwnerPrivateKey, digest2);
            errorSigner = ECDSA.recover(digest2, v, r, s);
        }

        vm.expectRevert(abi.encodeWithSelector(ERC2612InvalidSigner.selector, errorSigner, tokenOwner));
        vm.prank(attacker);
        nft.permit(permit.owner, permit.to, permit.value, permit.deadline, errorMsgHash, v, r, s);
    }

    /**
     * 测试NFTChange事件
     */
    function testTransfer() public {
        vm.expectEmit(false, false, false, true);
        emit NFTChange(tokenOwner, tokenTo, defaultTokenId, nft.tokenURI(defaultTokenId));
        vm.prank(tokenOwner);
        nft.transferFrom(tokenOwner, tokenTo, defaultTokenId);
    }

    /*****************************************************************单元测试 结束**********************************************************************/

    /*****************************************************************模糊测试 开始**********************************************************************/
    // function testFuzzPermit(
    //     address owner,
    //     address to,
    //     uint192 value,
    //     uint256 nonce,
    //     uint256 deadline,
    //     bytes32 msgHash,
    //     uint8 v,
    //     bytes32 r,
    //     bytes32 s
    // ) public {
    //     vm.assume(owner != address(0));
    //     vm.assume(to != address(0));
    //     vm.assume(deadline > block.timestamp); // 只测试未过期的

    //     // 获取当前 nonce，防止nonce不匹配导致无效
    //     uint256 currentNonce = nft.nonces(owner,value);

    //     // 只测试 nonce >= currentNonce，避免无效nonce
    //     vm.assume(nonce >= currentNonce);

    //     // 调用 permit，可能成功或失败，测试合约健壮性
    //     try nft.permit(owner, to, value, deadline,msgHash, v, r, s) {
    //         // 成功时，断言 allowance 被正确设置
    //         assertEq(nft.getApproved(value), to);
    //         assertEq(nft.nonces(owner,value), nonce + 1);
    //     } catch {
    //         // 失败时，不做断言，确保合约不会崩溃
    //     }
    // }
    /*****************************************************************模糊测试 结束**********************************************************************/

    /*****************************************************************形式化验证（符号执行） 开始**********************************************************************/
    function check_mintNFT(address to, string memory url) public {
        vm.prank(nftOwner);
        uint256 tokenId = nft.mintNFT(to, url);
        assertEq(nft.tokenURI(tokenId), url);
        assertEq(nft.ownerOf(tokenId), to);
    }

    /*****************************************************************形式化验证（符号执行） 结束**********************************************************************/
}
