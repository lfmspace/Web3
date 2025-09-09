// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import "forge-std/Test.sol";
import "../../src/NFTRent/RTNFT.sol";
import "../../src/NFTRent/RTRentMarket.sol";
import "../utils/SigUtils.sol";

contract RTRentMarketUintTest is Test {
    RTNFT public nft;
    RTRentMarket public market;
    address nftOwner;
    address marketOwner;
    address tokenMaker;
    address tokenTaker;
    uint256 tokenMakerPrivateKey;
    uint256 tokenTakerPrivateKey;
    uint256 defaultTokenId;
    uint256 takerStartBalance = 10000 ether;

    uint256 collateral = 1000 ether;
    uint256 dailyRent = 2 ether;
    uint256 rentalDuration = 10; //单位：天
    uint256 callValue = collateral + dailyRent * rentalDuration;
    uint256 deadlineTime = 1 hours;

    function setUp() public {
        nftOwner = makeAddr("nftOwner");
        marketOwner = makeAddr("marketOwner");
        nft = new RTNFT(nftOwner);
        market = new RTRentMarket(address(nft), marketOwner);
        //初始化租借方
        (tokenMaker, tokenMakerPrivateKey) = makeAddrAndKey("tokenMaker");
        //初始化承租方
        (tokenTaker, tokenTakerPrivateKey) = makeAddrAndKey("tokenTaker");
        vm.deal(tokenTaker, takerStartBalance);

        //NFT合约所有者铸造新的Token供测试使用
        vm.prank(nftOwner);
        defaultTokenId = nft.mintNFT(tokenMaker, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q");

        console.log("nftOwer is", nftOwner);
        console.log("marketOwner is", marketOwner);
        console.log("nft is", address(nft));
        console.log("market is", address(market));
        console.log("tokenMaker is", tokenMaker);
        console.log("tokenTaker is", tokenTaker);
    }

    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是未知（首次出租）
     */
    function testBorrow_willSucceed_stateUnkow() public {
        //获取tokenMaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenMakerPrivateKey, defaultTokenId, tokenMaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenMaker, defaultTokenId, dailyRent, collateral))));

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenMaker, uint96(callValue - dailyRent * rentalDuration), tokenTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.Borrowing);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        //验证订单变更事件
        vm.expectEmit(false, false, false, true);
        emit RTRentMarket.OrderChange(futureOrder);

        uint256 oldMarketBalance = address(market).balance;
        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        //承租动作
        vm.prank(tokenTaker);
        market.borrow{value: callValue}(defaultTokenId, dailyRent, rentalDuration, collateral, block.timestamp + deadlineTime, v, r, s);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }
        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);
        //验证出租方收入
        assertEq(market.makerBalances(tokenMaker), oldMakerBalance + dailyRent * rentalDuration);
        //验证Token新的归属权
        assertEq(nft.ownerOf(defaultTokenId), tokenTaker);
        //验证合同余额
        assertEq(address(market).balance, oldMarketBalance + callValue);
    }

    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是已赎回
     */
    function testBorrow_willSucceed_stateRedeemed() public {
        testTakerRedeem_willSucceed();
        testBorrow_willSucceed_stateUnkow();
    }

    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是已清算
     */
    function testBorrow_willSucceed_stateMakerClear() public {
        testMakerClear_willSucceed();
        //清算后NFT所有人归tokenTaker所有

        //获取tokenTaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenTakerPrivateKey, defaultTokenId, tokenTaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenTaker, defaultTokenId, dailyRent, collateral))));

        address selfTaker = makeAddr("selfTaker");
        vm.deal(selfTaker, 10000 ether);

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenTaker, uint96(callValue - dailyRent * rentalDuration), selfTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.Borrowing);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        //验证订单变更事件
        vm.expectEmit(false, false, false, true);
        emit RTRentMarket.OrderChange(futureOrder);

        uint256 oldMarketBalance = address(market).balance;
        uint256 oldMakerBalance = market.makerBalances(tokenTaker);
        //承租动作
        vm.prank(selfTaker);
        market.borrow{value: callValue}(defaultTokenId, dailyRent, rentalDuration, collateral, block.timestamp + deadlineTime, v, r, s);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }

        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);
        console.log("dasadfsafsadfsa ");
        //验证出租方收入
        assertEq(market.makerBalances(tokenTaker), oldMakerBalance + dailyRent * rentalDuration);
        //验证Token新的归属权
        assertEq(nft.ownerOf(defaultTokenId), selfTaker);
        //验证合同余额
        assertEq(address(market).balance, oldMarketBalance + callValue);
    }

    /**
     * 承租人租赁NFT
     * Revert分支：租用自己的NFT
     */
    function testBorrow_revert_selfBorrow() public {
        //获取tokenMaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenMakerPrivateKey, defaultTokenId, tokenMaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenMaker, defaultTokenId, dailyRent, collateral))));

        //验证
        vm.expectRevert("Can't borrow your own");

        vm.deal(tokenMaker, 10000 ether);
        //承租动作
        vm.prank(tokenMaker);
        market.borrow{value: callValue}(defaultTokenId, dailyRent, rentalDuration, collateral, block.timestamp + deadlineTime, v, r, s);
    }

    /**
     * 承租人租赁NFT
     * Revert分支：支付ETH不足，小于（押金+租金）
     */
    function testBorrow_revert_notEnoughPayment() public {
        //获取tokenMaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenMakerPrivateKey, defaultTokenId, tokenMaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenMaker, defaultTokenId, dailyRent, collateral))));

        //验证
        vm.expectRevert("Not enough payment");

        //承租动作
        vm.prank(tokenTaker);
        market.borrow{value: callValue - 1}(defaultTokenId, dailyRent, rentalDuration, collateral, block.timestamp + deadlineTime, v, r, s);
    }

    /**
     * 承租人租赁NFT
     * Revert分支：溢出（日租金*租借时间）
     */
    function testBorrow_revert_overflowDailyRentAndRentalDuration() public {
        uint256 selfDailyRent = type(uint256).max;
        uint256 selfRentalDuration = 3;
        //获取tokenMaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenMakerPrivateKey, defaultTokenId, tokenMaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenMaker, defaultTokenId, selfDailyRent, collateral))));

        //验证
        vm.expectRevert(stdError.arithmeticError);

        //承租动作
        vm.prank(tokenTaker);
        market.borrow{value: callValue}(defaultTokenId, selfDailyRent, selfRentalDuration, collateral, block.timestamp + deadlineTime, v, r, s);
    }

    // /**
    //  * 承租人租赁NFT
    //  * Revert分支：溢出（日租金*租借时间+押金）
    //  */
    // function _testBorrow_revert_overflowDailyRentAndRentalDurationAndCollateral() public {}
    // /**
    //  * 承租人租赁NFT
    //  * Revert分支：溢出（日租金*租借时间+出租人尚未提取的押金收益）
    //  */
    // function _testBorrow_revert_overflowDailyRentAndRentalDurationAndCollateral() public {}

    /**
     * 承租人租赁NFT
     * Revert分支：租借已出租的NFT
     */
    function testBorrow_revert_stateBorrowing() public {
        testBorrow_willSucceed_stateUnkow();

        console.log("nftNewOwner is", nft.ownerOf(defaultTokenId));
        //获取tokenMaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenTakerPrivateKey, defaultTokenId, tokenTaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenTaker, defaultTokenId, dailyRent, collateral))));

        //验证
        vm.expectRevert("NFT is borrowing");

        address selfTaker = makeAddr("selfTaker");
        vm.deal(selfTaker, 10000 ether);
        vm.prank(selfTaker);
        //再次借
        market.borrow{value: callValue}(defaultTokenId, dailyRent, rentalDuration, collateral, block.timestamp + deadlineTime, v, r, s);
    }

    /**
     * 承租人租赁NFT
     * Revert分支：签名已取消
     */
    function testBorrow_revert_signatureCancel() public {
        //获取tokenMaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenMakerPrivateKey, defaultTokenId, tokenMaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenMaker, defaultTokenId, dailyRent, collateral))));

        //取消签名
        vm.prank(tokenMaker);
        market.cancelBorrow(v, r, s);

        //验证
        vm.expectRevert("NFT not authorized to rent");
        //承租动作
        vm.prank(tokenTaker);
        market.borrow{value: callValue}(defaultTokenId, dailyRent, rentalDuration, collateral, block.timestamp + deadlineTime, v, r, s);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：未超时正常赎回
     **/
    function testTakerRedeem_willSucceed() public {
        testBorrow_willSucceed_stateUnkow();

        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(tokenTakerPrivateKey, defaultTokenId, tokenTaker, 1 hours, 0);

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenMaker, uint96(callValue - dailyRent * rentalDuration), tokenTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        //验证订单变更事件
        vm.expectEmit(false, false, false, true);
        emit RTRentMarket.OrderChange(futureOrder);
        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        //赎回
        vm.prank(tokenTaker);
        market.takerRedeem(defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }
        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);

        assertEq(nft.ownerOf(defaultTokenId), tokenMaker);
        //assertEq(tokenTaker.balance, takerStartBalance - dailyRent * rentalDuration);
        assertEq(address(market).balance, oldMarketBalance - collateral);
        assertEq(market.makerBalances(tokenMaker), oldMakerBalance);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：超时时间小于100天（超时后每天扣1%,最多扣100天）
     **/
    function testTakerRedeem_willSucceed_timeoutLess100Days() public {
        testBorrow_willSucceed_stateUnkow();

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenMaker, uint96(callValue - dailyRent * rentalDuration), tokenTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        //限制小于100，超时5天；
        uint256 overDays = 5;
        vm.warp(futureOrder.expiryTime + overDays * 86400);

        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(tokenTakerPrivateKey, defaultTokenId, tokenTaker, 1 hours, 0);

        //验证订单变更事件
        vm.expectEmit(false, false, false, true);
        emit RTRentMarket.OrderChange(futureOrder);
        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        //可赎回的押金
        uint256 redeemCollateral = ((100 - overDays) * futureOrder.collateral) / 100;

        //赎回
        vm.prank(tokenTaker);
        market.takerRedeem(defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }

        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);

        assertEq(nft.ownerOf(defaultTokenId), tokenMaker);
        assertEq(address(market).balance, oldMarketBalance - redeemCollateral);
        assertEq(market.makerBalances(tokenMaker), oldMakerBalance + futureOrder.collateral - redeemCollateral);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：超期大于100天（超时后每天扣1%,100天后押金清0）
     **/
    function testTakerRedeem_willSucceed_timeoutGreater100Days() public {
        testBorrow_willSucceed_stateUnkow();

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenMaker, uint96(callValue - dailyRent * rentalDuration), tokenTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);

        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        //限制超期大于100天；
        uint256 overDays = 101;
        vm.warp(futureOrder.expiryTime + overDays * 86400);

        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(tokenTakerPrivateKey, defaultTokenId, tokenTaker, 1 hours, 0);

        //验证订单变更事件
        vm.expectEmit(false, false, false, true);
        emit RTRentMarket.OrderChange(futureOrder);
        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        //可赎回的押金
        uint256 redeemCollateral = 0;

        //赎回
        vm.prank(tokenTaker);
        market.takerRedeem(defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }

        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);

        assertEq(nft.ownerOf(defaultTokenId), tokenMaker);
        assertEq(address(market).balance, oldMarketBalance - redeemCollateral);
        assertEq(market.makerBalances(tokenMaker), oldMakerBalance + futureOrder.collateral - redeemCollateral);
    }

    /**承租人赎回押金并归还NFT
     * revert分支：赎回人不是NFT的拥有者
     **/
    function testTakerRedeem_revert_notNFTOwner() public {
        testBorrow_willSucceed_stateUnkow();

        (address selfTaker, uint256 selfTakerPrivateKey) = makeAddrAndKey("selfTaker");
        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(selfTakerPrivateKey, defaultTokenId, selfTaker, 1 hours, 0);

        vm.expectRevert("Not nft owner");
        //赎回
        vm.prank(selfTaker);
        market.takerRedeem(defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);
    }

    /**承租人赎回押金并归还NFT
     * revert分支：NFT已被出租人清算（超过12天出租人可主动清算）
     **/
    function testTakerRedeem_revert_makeClear() public {
        testMakerClear_willSucceed();

        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(tokenTakerPrivateKey, defaultTokenId, tokenTaker, 1 hours, 0);

        vm.expectRevert("NFT is makerClear");
        //赎回
        vm.prank(tokenTaker);
        market.takerRedeem(defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);
    }

    // /**承租人赎回押金并归还NFT
    //  * revert分支：已赎回:此时nft所有者不是承租人，同testTakerRedeem_revert_notNFTOwner
    //  **/
    // function _testTakerRedeem_revert_redeemed() public {}

    /**出租人清算
     * willSucceed分支：超时已超过12天，正常清算
     **/
    function testMakerClear_willSucceed() public {
        testBorrow_willSucceed_stateUnkow();
        console.log("-----------------------testMakerClear_willSucceed call testBorrow_willSucceed_stateUnkow finished-----------------------------------");
        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        console.log("oldMarketBalance is", oldMarketBalance);
        console.log("oldMakerBalance is", oldMakerBalance);

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenMaker, uint96(callValue - dailyRent * rentalDuration), tokenTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.MakerClear);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }
        //验证订单变更事件
        vm.expectEmit(false, false, false, true);
        emit RTRentMarket.OrderChange(futureOrder);

        //设置超时12天
        uint256 overDays = 12;
        vm.warp(futureOrder.expiryTime + overDays * 86400);

        //清算
        vm.prank(tokenMaker);
        market.makerClear(defaultTokenId);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }
        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);

        assertEq(address(market).balance, oldMarketBalance - oldMakerBalance - futureOrder.collateral);
        assertEq(market.makerBalances(tokenMaker), 0);
    }

    /**出租人清算
     * revert分支：NFT已被赎回
     **/
    function testMakerClear_revert_redeemed() public {
        testTakerRedeem_willSucceed();

        //设置超时12天
        uint256 overDays = 12;
        vm.warp(uint88(block.timestamp + rentalDuration * 86400) + overDays * 86400);
        vm.expectRevert("NFT not borrowing");
        //清算
        vm.prank(tokenMaker);
        market.makerClear(defaultTokenId);
    }

    /**出租人清算
     * revert分支：NFT重复清算
     **/
    function testMakerClear_revert_repeatMakerClear() public {
        testMakerClear_willSucceed();

        vm.expectRevert("NFT not borrowing");
        //清算
        vm.prank(tokenMaker);
        market.makerClear(defaultTokenId);
    }

    /**出租人取消出租
     * WillSucceed分支：标记签名取消
     */
    function testSignatureCancel_willSucceed() public {
        //获取tokenMaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenMakerPrivateKey, defaultTokenId, tokenMaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenMaker, defaultTokenId, dailyRent, collateral))));

        vm.expectEmit(false, false, false, true);
        bytes32 sigHash = keccak256(abi.encode(r, s, v));
        emit RTRentMarket.SignatureCancel(tokenMaker, sigHash);

        //清算
        vm.prank(tokenMaker);
        market.cancelBorrow(v, r, s);

        assertTrue(market.cancelSignatures(tokenMaker, sigHash));
    }

    /**出租人提取租金
     * WillSucceed分支：租金大于0
     */
    function testMakerClaim_willSucceed() public {
        testBorrow_willSucceed_stateUnkow();

        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        vm.prank(tokenMaker);
        market.makerClaim();

        assertEq(market.makerBalances(tokenMaker), 0);
        assertEq(address(market).balance, oldMarketBalance - oldMakerBalance);
    }

    /**出租人提取租金
     * revert分支：租金为0
     */
    function testMakerClaim_revert_zertRent() public {
        address attacker = makeAddr("attacker");

        vm.expectRevert("No balances");
        vm.prank(attacker);
        market.makerClaim();
    }

    /**
     * 获取签名
     * @param s_ownerPrivateKey 签名者私钥
     * @param s_tokenId 签名转移的tokenId
     * @param s_owner 签名者地址
     * @param s_deadlineTime 签名截止日期
     * @return rtn_v
     * @return rtn_r
     * @return rtn_s
     */
    function getSignature(uint256 s_ownerPrivateKey, uint256 s_tokenId, address s_owner, uint256 s_deadlineTime, bytes32 s_msgHash) private view returns (uint8 rtn_v, bytes32 rtn_r, bytes32 rtn_s) {
        console.log("owner t is", s_owner);
        console.log("tokenId t is", s_tokenId);
        console.log("Nonce t is", nft.nonces(s_owner, uint192(s_tokenId)));
        console.log("deadline t is", block.timestamp + s_deadlineTime);
        console.log("msgHash t is", uint256(s_msgHash));
        //生成出租方签名
        SigUtils.Permit memory permit = SigUtils.Permit({owner: s_owner, to: address(market), value: s_tokenId, nonce: nft.nonces(s_owner, uint192(s_tokenId)), deadline: block.timestamp + s_deadlineTime, msgHash: s_msgHash});
        console.log("test permitHash is", uint256(keccak256(abi.encode(permit))));
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (rtn_v, rtn_r, rtn_s) = vm.sign(s_ownerPrivateKey, digest);
        address signer = ECDSA.recover(digest, rtn_v, rtn_r, rtn_s);
        console.log("recover signer is", signer);
        console.log("test msghash is", uint256(s_msgHash));
    }
}
