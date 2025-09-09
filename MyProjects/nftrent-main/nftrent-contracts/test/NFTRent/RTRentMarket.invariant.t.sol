// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import "forge-std/Test.sol";
import "../../src/NFTRent/RTNFT.sol";
import "../../src/NFTRent/RTRentMarket.sol";
import "../utils/SigUtils.sol";

contract RTRentMarketInvariantTest is Test {
    RTRentMarketHandler handler;
    RTNFT public nft;
    RTRentMarket public market;
    address nftOwner;
    address marketOwner;
    uint256 deadlineTime = 1 hours;

    function setUp() public {
        nftOwner = makeAddr("nftOwner");
        marketOwner = makeAddr("marketOwner");
        nft = new RTNFT(nftOwner);
        market = new RTRentMarket(address(nft), marketOwner);

        handler = new RTRentMarketHandler(nft, market, nftOwner, marketOwner);

        targetContract(address(handler));
    }
    struct Params {
        address tokenMaker;
        address tokenTaker;
        uint256 tokenMakerPrivateKey;
        uint256 tokenTakerPrivateKey;
        uint256 dailyRent;
        uint256 rentalDuration;
        uint96 collateral;
        uint96 callValue;
        uint8 v;
        bytes32 r;
        bytes32 s;
        uint256 defaultTokenId;
    }
    Params params;
    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是未知（首次出租）
     */
    function invariant_testBorrow_willSucceed_stateUnkow() public {
        params = createParams();

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(params.tokenMaker, uint96(params.callValue - params.dailyRent * params.rentalDuration), params.tokenTaker, uint88(block.timestamp + params.rentalDuration * 86400), RTRentMarket.OrderState.Borrowing);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        uint256 oldMarketBalance = address(market).balance;
        uint256 oldMakerBalance = market.makerBalances(params.tokenMaker);
        //承租动作
        vm.prank(params.tokenTaker);
        market.borrow{value: params.callValue}(params.defaultTokenId, params.dailyRent, params.rentalDuration, params.collateral, block.timestamp + deadlineTime, params.v, params.r, params.s);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(params.defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }
        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);
        //验证出租方收入
        assertEq(market.makerBalances(params.tokenMaker), oldMakerBalance + params.dailyRent * params.rentalDuration);
        //验证Token新的归属权
        assertEq(nft.ownerOf(params.defaultTokenId), params.tokenTaker);
        //验证合同余额
        assertEq(address(market).balance, oldMarketBalance + params.callValue);
        console.log(" invariant_testBorrow_willSucceed_stateUnkow call end");
        assert(true);
    }

    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是已赎回
     */
    function invariant_testBorrow_willSucceed_stateRedeemed() public {
        invariant_testTakerRedeem_willSucceed();

        invariant_testBorrow_willSucceed_stateUnkow();
        console.log(" invariant_testBorrow_willSucceed_stateRedeemed call end");
        assert(true);
    }

    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是已清算
     */
    function invariant_testBorrow_willSucceed_stateMakerClear() public {
        params = createParams();
        invariant_testMakerClear_willSucceed();
        console.log("-----------------------testBorrow_willSucceed_stateMakerClear call testMakerClear_willSucceed finished-----------------------------------");
        //清算后NFT所有人归tokenTaker所有
        //获取tokenTaker签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(params.tokenTakerPrivateKey, params.defaultTokenId, params.tokenTaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(params.tokenTaker, params.defaultTokenId, params.dailyRent, params.collateral))));

        address selfTaker = makeAddr("selfTaker");
        vm.deal(selfTaker, type(uint256).max);

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(params.tokenTaker, uint96(params.callValue - params.dailyRent * params.rentalDuration), selfTaker, uint88(block.timestamp + params.rentalDuration * 86400), RTRentMarket.OrderState.Borrowing);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        // //验证订单变更事件
        // vm.expectEmit(false, false, false, true);
        // emit RTRentMarket.OrderChange(futureOrder);

        uint256 oldMarketBalance = address(market).balance;
        uint256 oldMakerBalance = market.makerBalances(params.tokenTaker);
        //承租动作
        vm.prank(selfTaker);
        market.borrow{value: params.callValue}(params.defaultTokenId, params.dailyRent, params.rentalDuration, params.collateral, block.timestamp + deadlineTime, v, r, s);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(params.defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }

        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);
        console.log("step tag testBorrow_willSucceed_stateMakerClear assertEq(futureOrderHash, afterOrderHash) after");
        //验证出租方收入
        assertEq(market.makerBalances(params.tokenTaker), oldMakerBalance + params.dailyRent * params.rentalDuration);
        //验证Token新的归属权
        assertEq(nft.ownerOf(params.defaultTokenId), selfTaker);
        //验证合同余额
        assertEq(address(market).balance, oldMarketBalance + params.callValue);
        console.log(" invariant_testBorrow_willSucceed_stateMakerClear call end");
        assert(true);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：未超时正常赎回
     **/
    function invariant_testTakerRedeem_willSucceed() public {
        params = createParams();

        invariant_testBorrow_willSucceed_stateUnkow();
        console.log("-----------------------invariant_testTakerRedeem_willSucceed call invariant_testBorrow_willSucceed_stateUnkow finished-----------------------------------");

        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(params.tokenTakerPrivateKey, params.defaultTokenId, params.tokenTaker, 1 hours, 0);

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(params.tokenMaker, uint96(params.callValue - params.dailyRent * params.rentalDuration), params.tokenTaker, uint88(block.timestamp + params.rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        uint256 oldMakerBalance = market.makerBalances(params.tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        //赎回
        vm.prank(params.tokenTaker);
        market.takerRedeem(params.defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(params.defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }
        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);

        assertEq(nft.ownerOf(params.defaultTokenId), params.tokenMaker);
        //assertEq(tokenTaker.balance, takerStartBalance - dailyRent * rentalDuration);
        assertEq(address(market).balance, oldMarketBalance - futureOrder.collateral);
        assertEq(market.makerBalances(params.tokenMaker), oldMakerBalance);
        console.log(" invariant_testTakerRedeem_willSucceed call end");
        assert(true);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：超时时间小于100天（超时后每天扣1%,最多扣100天）
     **/
    function invariant_testTakerRedeem_willSucceed_timeoutLess100Days() public {
        //Params memory params = createParams();
        //限制小于等于100
        uint256 overDays = 99;

        invariant_testBorrow_willSucceed_stateUnkow();
        console.log("-----------------------testTakerRedeem_willSucceed_timeoutLess100Days call testBorrow_willSucceed_stateUnkow finished-----------------------------------");

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(params.tokenMaker, uint96(params.callValue - params.dailyRent * params.rentalDuration), params.tokenTaker, uint88(block.timestamp + params.rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        vm.warp(futureOrder.expiryTime + overDays * 86400);

        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(params.tokenTakerPrivateKey, params.defaultTokenId, params.tokenTaker, 1 hours, 0);

        // //验证订单变更事件
        // vm.expectEmit(false, false, false, true);
        // emit RTRentMarket.OrderChange(futureOrder);
        uint256 oldMakerBalance = market.makerBalances(params.tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        //可赎回的押金
        uint256 redeemCollateral = ((100 - overDays) * futureOrder.collateral) / 100;

        //赎回
        vm.prank(params.tokenTaker);
        market.takerRedeem(params.defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(params.defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }

        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);

        assertEq(nft.ownerOf(params.defaultTokenId), params.tokenMaker);
        console.log("step tag testTakerRedeem_willSucceed_timeoutLess100Days assertEq(nft.ownerOf(defaultTokenId), tokenMaker) after");
        assertEq(address(market).balance, oldMarketBalance - redeemCollateral);
        assertEq(market.makerBalances(params.tokenMaker), oldMakerBalance + futureOrder.collateral - redeemCollateral);
        console.log(" invariant_testTakerRedeem_willSucceed_timeoutLess100Days call end");
        assert(true);
    }

    /**承租人赎回押金并归还NFT
     * WillSucceed分支：超期大于100天（超时后每天扣1%,100天后押金清0）
     **/
    function invariant_testTakerRedeem_willSucceed_timeoutGreater100Days() public {
        //Params memory params = createParams();

        invariant_testBorrow_willSucceed_stateUnkow();
        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(params.tokenMaker, uint96(params.callValue - params.dailyRent * params.rentalDuration), params.tokenTaker, uint88(block.timestamp + params.rentalDuration * 86400), RTRentMarket.OrderState.Redeemed);

        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        //限制超期大于100天；
        uint256 overDays = 200;
        vm.warp(futureOrder.expiryTime + overDays * 86400);
        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(params.tokenTakerPrivateKey, params.defaultTokenId, params.tokenTaker, 1 hours, 0);

        // //验证订单变更事件
        // vm.expectEmit(false, false, false, true);
        // emit RTRentMarket.OrderChange(futureOrder);
        uint256 oldMakerBalance = market.makerBalances(params.tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        //可赎回的押金
        uint256 redeemCollateral = 0;

        //赎回
        vm.prank(params.tokenTaker);
        market.takerRedeem(params.defaultTokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(params.defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }

        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);

        assertEq(nft.ownerOf(params.defaultTokenId), params.tokenMaker);
        assertEq(address(market).balance, oldMarketBalance - redeemCollateral);
        assertEq(market.makerBalances(params.tokenMaker), oldMakerBalance + futureOrder.collateral - redeemCollateral);
        console.log(" invariant_testTakerRedeem_willSucceed_timeoutGreater100Days call end");
        assert(true);
    }

    /**出租人清算
     * willSucceed分支：超时已超过12天，正常清算
     **/
    function invariant_testMakerClear_willSucceed() public {
        //Params memory params = createParams();
        //设置超时超过12天
        uint256 overDays = 20;

        invariant_testBorrow_willSucceed_stateUnkow();
        console.log("-----------------------testMakerClear_willSucceed call testBorrow_willSucceed_stateUnkow finished-----------------------------------");
        uint256 oldMakerBalance = market.makerBalances(params.tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        console.log("oldMarketBalance is", oldMarketBalance);
        console.log("oldMakerBalance is", oldMakerBalance);

        RTRentMarket.OrderInfo memory futureOrder = RTRentMarket.OrderInfo(params.tokenMaker, uint96(params.callValue - params.dailyRent * params.rentalDuration), params.tokenTaker, uint88(block.timestamp + params.rentalDuration * 86400), RTRentMarket.OrderState.MakerClear);
        bytes32 futureOrderHash;
        {
            futureOrderHash = keccak256(abi.encode(futureOrder.maker, futureOrder.collateral, futureOrder.taker, futureOrder.expiryTime, futureOrder.orderState));
        }

        vm.warp(futureOrder.expiryTime + overDays * 86400);
        console.log("step tag testMakerClear_willSucceed vm.warp(futureOrder.expiryTime + overDays * 86400) after");
        //清算
        vm.prank(params.tokenMaker);
        market.makerClear(params.defaultTokenId);

        bytes32 afterOrderHash;
        {
            (address makerRtn, uint96 collateralRtn, address takerRtn, uint88 expiryTimeRtn, RTRentMarket.OrderState orderStateRtn) = market.rentOrder(params.defaultTokenId);
            afterOrderHash = keccak256(abi.encode(makerRtn, collateralRtn, takerRtn, expiryTimeRtn, orderStateRtn));
        }
        //验证新订单
        assertEq(futureOrderHash, afterOrderHash);
        console.log("step tag testMakerClear_willSucceed assertEq(futureOrderHash, afterOrderHash); after");

        assertEq(address(market).balance, oldMarketBalance - oldMakerBalance - futureOrder.collateral);
        assertEq(market.makerBalances(params.tokenMaker), 0);
        console.log(" invariant_testMakerClear_willSucceed call end");
        assert(true);
    }

    /**出租人取消出租
     * WillSucceed分支：标记签名取消
     */
    function invariant_testSignatureCancel_willSucceed() public {
        params = createParams();
        // vm.expectEmit(false, false, false, true);
        bytes32 sigHash = keccak256(abi.encode(params.r, params.s, params.v));
        //emit RTRentMarket.SignatureCancel(tokenMaker, sigHash);

        //清算
        vm.prank(params.tokenMaker);
        market.cancelBorrow(params.v, params.r, params.s);

        assertTrue(market.cancelSignatures(params.tokenMaker, sigHash));
    }

    /**出租人提取租金
     * WillSucceed分支：租金大于0
     */
    function invariant_testMakerClaim_willSucceed() public {
        //Params memory params = createParams();
        invariant_testBorrow_willSucceed_stateUnkow();

        uint256 oldMakerBalance = market.makerBalances(params.tokenMaker);
        uint256 oldMarketBalance = address(market).balance;

        vm.prank(params.tokenMaker);
        market.makerClaim();

        assertEq(market.makerBalances(params.tokenMaker), 0);
        assertEq(address(market).balance, oldMarketBalance - oldMakerBalance);
        console.log(" invariant_testMakerClaim_willSucceed call end");
        assert(true);
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
        //console.log("test permitHash is", uint256(keccak256(abi.encode(permit))));
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (rtn_v, rtn_r, rtn_s) = vm.sign(s_ownerPrivateKey, digest);
    }

    function createParams() private returns (Params memory _params) {
        (address tokenMaker, uint256 tokenMakerPrivateKey) = makeAddrAndKey(string(abi.encodePacked("tokenMaker")));
        (address tokenTaker, uint256 tokenTakerPrivateKey) = makeAddrAndKey(string(abi.encodePacked("tokenTaker")));
        vm.deal(tokenMaker, type(uint96).max);
        vm.deal(tokenTaker, type(uint96).max);

        //NFT合约所有者铸造新的Token供测试使用
        vm.prank(nftOwner);
        uint256 defaultTokenId = nft.mintNFT(tokenMaker, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q");

        bool assumeCondition;
        uint256 dailyRent;
        uint256 rentalDuration;
        uint96 collateral;
        uint96 callValue;
        while (!assumeCondition) {
            dailyRent = vm.randomUint() % 256;
            rentalDuration = vm.randomUint() % 256;
            collateral = uint96(vm.randomUint()) % 256;
            callValue = uint96(vm.randomUint()) % type(uint48).max;

            assumeCondition = dailyRent > 0 && rentalDuration > 0 && collateral > 0 && callValue < tokenMaker.balance && dailyRent < type(uint256).max - 1 && rentalDuration < type(uint256).max - 1 && callValue > collateral && (callValue - collateral) / rentalDuration > dailyRent + 1 && (callValue - collateral) / dailyRent > rentalDuration + 1 && rentalDuration + 1 < type(uint96).max / dailyRent && dailyRent + 1 <= type(uint96).max / rentalDuration;
        }

        //获取tokenMaker.adr签名
        (uint8 v, bytes32 r, bytes32 s) = getSignature(tokenMakerPrivateKey, defaultTokenId, tokenMaker, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(tokenMaker, defaultTokenId, dailyRent, collateral))));

        _params = Params(tokenMaker, tokenTaker, tokenMakerPrivateKey, tokenTakerPrivateKey, dailyRent, rentalDuration, collateral, callValue, v, r, s, defaultTokenId);
    }
}

contract RTRentMarketHandler is Test {
    RTNFT public nft;
    RTRentMarket public market;
    address nftOwner;
    address marketOwner;
    uint256 deadlineTime = 10000 days;
    //构建的模拟用户长度
    uint256 simulationUserLength = 100;
    //构建的模拟用户&出租信息&授权签名信息
    struct SimulationUser {
        address adr;
        uint256 privateKey;
        uint96 tokenId;
        uint8 v;
        bytes32 r;
        bytes32 s;
        uint256 dailyRent;
        uint256 rentalDuration;
        uint96 collateral;
        uint96 callValue;
        uint256 deadline;
        uint256[] makerUserIndex; //作为承租人时NFT的出租人索引
        uint256[] takerUserIndex; //作为出租人时租赁NFT的人索引
    }
    SimulationUser[] userArray;

    constructor(RTNFT _nft, RTRentMarket _market, address _nftOwner, address _marketOwner) {
        nft = _nft;
        market = _market;
        nftOwner = _nftOwner;
        marketOwner = _marketOwner;
        createSimulationUser();
    }

    /**
     * 承租人租赁NFT
     * WillSucceed分支：NFT的订单状态是未知（首次出租）
     */
    function testBorrow_allCondition(uint256 makerIndexSeed, uint256 takerIndexSeed) public {
        uint256 makerIndex = makerIndexSeed % simulationUserLength;
        uint256 takerIndex = takerIndexSeed % simulationUserLength;
        //if (makerIndex == takerIndex) takerIndex = (makerIndex + 1) % simulationUserLength;

        SimulationUser storage tokenMakerUser = userArray[makerIndex];
        SimulationUser storage tokenTakerUser = userArray[takerIndex];
        address tokenTaker = tokenTakerUser.adr;
        uint256 dailyRent = tokenMakerUser.dailyRent;
        uint256 rentalDuration = tokenMakerUser.rentalDuration;
        uint96 collateral = tokenMakerUser.collateral;
        uint96 callValue = tokenMakerUser.callValue;
        uint256 deadline = tokenMakerUser.deadline;
        uint256 defaultTokenId = tokenMakerUser.tokenId;
        uint8 v = tokenMakerUser.v;
        bytes32 r = tokenMakerUser.r;
        bytes32 s = tokenMakerUser.s;

        tokenTakerUser.makerUserIndex.push(makerIndex);
        tokenMakerUser.takerUserIndex.push(takerIndex);

        //承租动作
        vm.prank(tokenTaker);
        market.borrow{value: callValue}(defaultTokenId, dailyRent, rentalDuration, collateral, deadline, v, r, s);
    }

    /**
     * 承租人赎回押金并归还NFT
     * 所有可达路径
     **/
    function testTakerRedeem_allCondition(uint256 makerIndexSeed, uint256 takerIndexSeed, uint8 overDays) public {
        SimulationUser storage tokenTakerUser = userArray[takerIndexSeed % simulationUserLength];

        SimulationUser storage tokenMakerUser;
        if (tokenTakerUser.makerUserIndex.length > 0) {
            tokenMakerUser = userArray[tokenTakerUser.makerUserIndex[tokenTakerUser.makerUserIndex.length - 1]];
            tokenTakerUser.makerUserIndex.pop();
        } else {
            tokenMakerUser = userArray[makerIndexSeed % simulationUserLength];
            testBorrow_allCondition(makerIndexSeed, takerIndexSeed);
            console.log("-----------------------testTakerRedeem_allCondition call testBorrow_allCondition_stateUnkow finished-----------------------------------");
        }
        address tokenTaker = tokenTakerUser.adr;
        // uint8 vTaker = tokenTakerUser.v;
        // bytes32 rTaker = tokenTakerUser.r;
        // bytes32 sTaker = tokenTakerUser.s;
        uint256 rentalDuration = tokenMakerUser.rentalDuration;

        vm.warp(block.timestamp + rentalDuration * 86400 + overDays * 86400);

        (uint8 vTaker, bytes32 rTaker, bytes32 sTaker) = getSignature(tokenTakerUser.privateKey, tokenMakerUser.tokenId, tokenTaker, 1 hours, 0);

        //赎回
        vm.prank(tokenTaker);
        market.takerRedeem(tokenMakerUser.tokenId, block.timestamp + 1 hours, vTaker, rTaker, sTaker);
    }

    /**
     * 出租人清算
     * 所有可达路径
     **/
    function testMakerClear_allCondition(uint256 makerIndexSeed, uint256 takerIndexSeed, uint8 overDays) public {
        SimulationUser storage tokenTakerUser = userArray[takerIndexSeed % simulationUserLength];

        SimulationUser storage tokenMakerUser;
        if (tokenTakerUser.makerUserIndex.length > 0) {
            tokenMakerUser = userArray[tokenTakerUser.makerUserIndex[tokenTakerUser.makerUserIndex.length - 1]];
            tokenTakerUser.makerUserIndex.pop();
        } else {
            tokenMakerUser = userArray[makerIndexSeed % simulationUserLength];
            testBorrow_allCondition(makerIndexSeed, takerIndexSeed);

            console.log("-----------------------testMakerClear_allCondition call testBorrow_allCondition_stateUnkow finished-----------------------------------");
        }

        address tokenMaker = tokenMakerUser.adr;

        uint256 rentalDuration = tokenMakerUser.rentalDuration;

        console.log("step tag testMakerClear_allCondition vm.warp(futureOrder.expiryTime + overDays * 86400) after");
        vm.warp(block.timestamp + rentalDuration * 86400 + overDays * 86400);
        //清算
        vm.prank(tokenMaker);
        market.makerClear(tokenMakerUser.tokenId);
    }

    /**
     * 出租人提取租金
     * 所有可达路径
     */
    function testMakerClaim_allCondition(uint256 makerIndexSeed, uint256 takerIndexSeed, bool makerBalanceMustGreater0) public {
        SimulationUser storage tokenMakerUser = userArray[vm.randomUint() % simulationUserLength];
        address tokenMaker = tokenMakerUser.adr;
        uint256 oldMakerBalance = market.makerBalances(tokenMaker);
        if (makerBalanceMustGreater0 && oldMakerBalance <= 0) {
            testBorrow_allCondition(makerIndexSeed, takerIndexSeed);
        }

        vm.prank(tokenMaker);
        market.makerClaim();
    }

    /**
     * 出租人取消出租
     * 所有可达路径
     */
    function testSignatureCancel_allCondition() public {
        SimulationUser storage tokenMakerUser = userArray[vm.randomUint() % simulationUserLength];
        uint8 v = tokenMakerUser.v;
        bytes32 r = tokenMakerUser.r;
        bytes32 s = tokenMakerUser.s;
        address tokenMaker = tokenMakerUser.adr;

        //清算
        vm.prank(tokenMaker);
        market.cancelBorrow(v, r, s);
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
        //console.log("test permitHash is", uint256(keccak256(abi.encode(permit))));
        bytes32 digest = SigUtils.getTypedDataHash(permit, nft.DOMAIN_SEPARATOR());
        (rtn_v, rtn_r, rtn_s) = vm.sign(s_ownerPrivateKey, digest);
    }

    /**生成模拟用户，并将用户NFT全部授权租借 */
    function createSimulationUser() private {
        for (uint256 i = 0; i < simulationUserLength; i++) {
            (address user, uint256 userPrivateKey) = makeAddrAndKey(string(abi.encodePacked("user", i)));
            vm.deal(user, type(uint96).max);
            //NFT合约所有者铸造新的Token供测试使用
            vm.prank(nftOwner);
            uint256 tokenId = nft.mintNFT(user, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreih5j57zgxszjn2mujjxnyqscckqig5llqe3b5u3dzboj44c4yh44q");

            bool assumeCondition;
            uint256 dailyRent;
            uint16 rentalDuration;
            uint96 collateral;
            uint96 callValue;
            while (!assumeCondition) {
                dailyRent = vm.randomUint() % 256;
                rentalDuration = uint16(vm.randomUint()) % 256;
                collateral = uint96(vm.randomUint()) % 256;
                callValue = uint96(vm.randomUint()) % type(uint48).max;

                assumeCondition = dailyRent > 0 && rentalDuration > 0 && collateral > 0 && callValue < user.balance && dailyRent < type(uint256).max - 1 && rentalDuration < type(uint256).max - 1 && callValue > collateral && (callValue - collateral) / rentalDuration > dailyRent + 1 && (callValue - collateral) / dailyRent > rentalDuration + 1 && rentalDuration + 1 < type(uint96).max / dailyRent && dailyRent + 1 <= type(uint96).max / rentalDuration;
            }

            //获取tokenMaker.adr签名
            (uint8 v, bytes32 r, bytes32 s) = getSignature(userPrivateKey, tokenId, user, deadlineTime, keccak256(abi.encode(RTRentMarket.BorrowInfo(user, tokenId, dailyRent, collateral))));

            userArray.push(SimulationUser({adr: user, privateKey: userPrivateKey, tokenId: uint96(tokenId), v: v, r: r, s: s, dailyRent: dailyRent, rentalDuration: rentalDuration, collateral: collateral, callValue: callValue, deadline: block.timestamp + deadlineTime, makerUserIndex: new uint256[](0), takerUserIndex: new uint256[](0)}));
        }
    }
}
