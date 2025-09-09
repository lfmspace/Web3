// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import "forge-std/Test.sol";
import "../../src/NFTRent/RTNFT.sol";
import "../../src/NFTRent/RTRentMarket.sol";
import "../utils/SigUtils.sol";

contract RTRentMarketFuzzTest is Test {
    RTNFT public nft;
    RTRentMarket public market;
    address nftOwner;
    address marketOwner;
    address tokenMaker;
    address tokenTaker;
    uint256 tokenMakerPrivateKey;
    uint256 tokenTakerPrivateKey;
    uint256 defaultTokenId;
    uint256 deadlineTime = 1 hours;

    modifier assumeOverflow(
        uint256 dailyRent,
        uint256 rentalDuration,
        uint96 collateral,
        uint96 callValue
    ) {
        bool assumeCondition = dailyRent > 0 && rentalDuration > 0 && collateral > 0 && callValue < tokenTaker.balance && dailyRent < type(uint256).max - 1 && rentalDuration < type(uint256).max - 1 && callValue > collateral && (callValue - collateral) / rentalDuration > dailyRent + 1 && (callValue - collateral) / dailyRent > rentalDuration + 1 && rentalDuration + 1 < type(uint96).max / dailyRent && dailyRent + 1 <= type(uint96).max / rentalDuration;
        // //确保不溢出
        //vm.assume(assumeCondition);

        if (!assumeCondition) return;

        _;
    }

    function setUp() public {
        nftOwner = makeAddr("nftOwner");
        marketOwner = makeAddr("marketOwner");
        nft = new RTNFT(nftOwner);
        market = new RTRentMarket(address(nft), marketOwner);
        //初始化租借方
        (tokenMaker, tokenMakerPrivateKey) = makeAddrAndKey("tokenMaker");
        //初始化承租方
        (tokenTaker, tokenTakerPrivateKey) = makeAddrAndKey("tokenTaker");
        vm.deal(tokenTaker, type(uint96).max);
        vm.deal(tokenMaker, type(uint96).max);

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
    function testBorrow_willSucceed_stateUnkow(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
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
    function testBorrow_willSucceed_stateRedeemed(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
        testTakerRedeem_willSucceed(dailyRent, rentalDuration, collateral, callValue);
        testBorrow_willSucceed_stateUnkow(dailyRent, rentalDuration, collateral, callValue);
    }

    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是已清算
     */
    function testBorrow_willSucceed_stateMakerClear(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
        testMakerClear_willSucceed(dailyRent, rentalDuration, collateral, callValue);
        console.log("-----------------------testBorrow_willSucceed_stateMakerClear call testMakerClear_willSucceed finished-----------------------------------");
        //清算后NFT所有人归tokenTaker所有
        //获取tokenTaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenTakerPrivateKey, defaultTokenId, tokenTaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenTaker, defaultTokenId, dailyRent, collateral))));

        address selfTaker = makeAddr("selfTaker");
        vm.deal(selfTaker, type(uint256).max);

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
        console.log("step tag testBorrow_willSucceed_stateMakerClear assertEq(futureOrderHash, afterOrderHash) after");
        //验证出租方收入
        assertEq(market.makerBalances(tokenTaker), oldMakerBalance + dailyRent * rentalDuration);
        //验证Token新的归属权
        assertEq(nft.ownerOf(defaultTokenId), selfTaker);
        //验证合同余额
        assertEq(address(market).balance, oldMarketBalance + callValue);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：未超时正常赎回
     **/
    function testTakerRedeem_willSucceed(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
        testBorrow_willSucceed_stateUnkow(dailyRent, rentalDuration, collateral, callValue);
        console.log("-----------------------testTakerRedeem_willSucceed call testBorrow_willSucceed_stateUnkow finished-----------------------------------");

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
        assertEq(address(market).balance, oldMarketBalance - futureOrder.collateral);
        assertEq(market.makerBalances(tokenMaker), oldMakerBalance);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：超时时间小于100天（超时后每天扣1%,最多扣100天）
     **/
    function testTakerRedeem_willSucceed_timeoutLess100Days(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
        // dailyRent = 1;
        // rentalDuration = 6504573241010217419203242;
        // collateral = 85607;
        // callValue = 8259525335848090201970450432;
        //限制小于等于100
        uint256 overDays = vm.randomUint();
        vm.assume(overDays <= 100);

        testBorrow_willSucceed_stateUnkow(dailyRent, rentalDuration, collateral, callValue);
        console.log("-----------------------testTakerRedeem_willSucceed_timeoutLess100Days call testBorrow_willSucceed_stateUnkow finished-----------------------------------");

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenMaker, uint96(callValue - dailyRent * rentalDuration), tokenTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

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
        console.log("step tag testTakerRedeem_willSucceed_timeoutLess100Days assertEq(nft.ownerOf(defaultTokenId), tokenMaker) after");
        assertEq(address(market).balance, oldMarketBalance - redeemCollateral);
        assertEq(market.makerBalances(tokenMaker), oldMakerBalance + futureOrder.collateral - redeemCollateral);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：超期大于100天（超时后每天扣1%,100天后押金清0）
     **/
    function testTakerRedeem_willSucceed_timeoutGreater100Days(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
        //限制超期大于100天；
        uint256 overDays = vm.randomUint();
        vm.assume(overDays > 100 && overDays < 36500);

        testBorrow_willSucceed_stateUnkow(dailyRent, rentalDuration, collateral, callValue);

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(tokenMaker, uint96(callValue - dailyRent * rentalDuration), tokenTaker, uint88(block.timestamp + rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);

        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

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

    /**出租人清算
     * willSucceed分支：超时已超过12天，正常清算
     **/
    function testMakerClear_willSucceed(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
        //设置超时超过12天
        uint256 overDays = vm.randomUint();
        vm.assume(overDays > 12 && overDays < 36500);

        testBorrow_willSucceed_stateUnkow(dailyRent, rentalDuration, collateral, callValue);
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

        vm.warp(futureOrder.expiryTime + overDays * 86400);
        console.log("step tag testMakerClear_willSucceed vm.warp(futureOrder.expiryTime + overDays * 86400) after");
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
        console.log("step tag testMakerClear_willSucceed assertEq(futureOrderHash, afterOrderHash); after");

        assertEq(address(market).balance, oldMarketBalance - oldMakerBalance - futureOrder.collateral);
        assertEq(market.makerBalances(tokenMaker), 0);
    }

    /**出租人取消出租
     * WillSucceed分支：标记签名取消
     */
    function testSignatureCancel_willSucceed(uint8 v, bytes32 r, bytes32 s) public {
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
    function testMakerClaim_willSucceed(uint256 dailyRent, uint256 rentalDuration, uint96 collateral, uint96 callValue) public assumeOverflow(dailyRent, rentalDuration, collateral, callValue) {
        testBorrow_willSucceed_stateUnkow(dailyRent, rentalDuration, collateral, callValue);

        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        vm.prank(tokenMaker);
        market.makerClaim();

        assertEq(market.makerBalances(tokenMaker), 0);
        assertEq(address(market).balance, oldMarketBalance - oldMakerBalance);
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
        //生成出租方签名
        SigUtils.Permit memory permit = SigUtils.Permit({owner: s_owner, to: address(market), value: s_tokenId, nonce: nft.nonces(s_owner, uint192(s_tokenId)), deadline: block.timestamp + s_deadlineTime, msgHash: s_msgHash});
        console.log("test permitHash is", uint256(keccak256(abi.encode(permit))));
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (rtn_v, rtn_r, rtn_s) = vm.sign(s_ownerPrivateKey, digest);
    }
}
