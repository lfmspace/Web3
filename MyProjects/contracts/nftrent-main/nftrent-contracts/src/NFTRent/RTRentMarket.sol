// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

import "./RTNFT.sol";
import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/Address.sol";

contract RTRentMarket is Ownable {
    using Address for address payable;
    enum OrderState {
        Unknown, //未知
        Borrowing, //租借中
        Redeemed, //已赎回
        MakerClear //抵押超期出租方放弃
    }

    struct OrderInfo {
        address maker; //nft提供者
        uint96 collateral; //抵押eth数量
        address taker; //nft租借者
        uint88 expiryTime; //租借截止日期
        OrderState orderState; //订单状态
    }

    struct BorrowInfo {
        address maker; //nft提供者
        uint256 tokenId;
        uint256 dailyRent; //每日租金
        uint256 collateral; //押金
    }

    RTNFT internal immutable _nft;
    mapping(uint256 => OrderInfo) public rentOrder; //租借订单列表
    mapping(address => mapping(bytes32 => bool)) public cancelSignatures; //记录取消的签名
    mapping(address => uint256) public makerBalances; //记录收入

    event OrderChange(OrderInfo borrowInfo);
    event SignatureCancel(address from, bytes32 sigHash);

    constructor(address nft, address nfOwner) Ownable(nfOwner) {
        _nft = RTNFT(nft);
    }

    /**
     * 租借NFT
     * @param tokenId 需要借的NFTID
     * @param dailyRent 每日租金
     * @param rentalDuration 租借时长，单位：天
     * @param collateral 抵押eth数量
     * @param deadline 出租房授权出租签名的截止日期
     * @param v 签名v
     * @param r 签名r
     * @param s 签名s
     */
    function borrow(uint256 tokenId, uint256 dailyRent, uint256 rentalDuration, uint256 collateral, uint256 deadline, uint8 v, bytes32 r, bytes32 s) public payable {
        require(rentOrder[tokenId].orderState != OrderState.Borrowing, "NFT is borrowing");

        require(msg.value >= dailyRent * rentalDuration + collateral && msg.value > dailyRent * rentalDuration && msg.value > collateral, "Not enough payment");

        address tokenOwner = _nft.ownerOf(tokenId);
        require(msg.sender != tokenOwner, "Can't borrow your own");
        require(!cancelSignatures[tokenOwner][keccak256(abi.encode(r, s, v))], "NFT not authorized to rent");

        OrderInfo memory order = OrderInfo(tokenOwner, uint96(msg.value - dailyRent * rentalDuration), msg.sender, uint88(block.timestamp + rentalDuration * 86400), OrderState.Borrowing);
        rentOrder[tokenId] = order;
        makerBalances[tokenOwner] += dailyRent * rentalDuration;
        emit OrderChange(order);

        BorrowInfo memory borrowInfo = BorrowInfo(tokenOwner, tokenId, dailyRent, collateral);

        _nft.permit(tokenOwner, address(this), tokenId, deadline, keccak256(abi.encode(borrowInfo)), v, r, s);
        _nft.safeTransferFrom(tokenOwner, msg.sender, tokenId);
    }

    /**
     * 取消出租信息：将签名设置为false表示不可用
     * @param v 签名v
     * @param r 签名r
     * @param s 签名s
     */
    function cancelBorrow(uint8 v, bytes32 r, bytes32 s) public {
        bytes32 sigHash = keccak256(abi.encode(r, s, v));
        cancelSignatures[msg.sender][sigHash] = true;
        emit SignatureCancel(msg.sender, sigHash);
    }

    /**
     * 借方赎回押金并归还NFT
     * 可提前赎回，但已缴租金不退
     * 使用签名授权一次性赎回，无需借方另行授权
     * @param tokenId 租借的代币ID
     * @param deadline 签名截止日期
     * @param v 签名v
     * @param r 签名r
     * @param s 签名s
     */
    function takerRedeem(uint256 tokenId, uint256 deadline, uint8 v, bytes32 r, bytes32 s) public {
        OrderInfo storage order = rentOrder[tokenId];
        require(order.taker == msg.sender, "Not nft owner");
        require(order.orderState == OrderState.Borrowing, "NFT is makerClear");

        //计算需要退回的金额
        uint256 redeemAmount;
        if (block.timestamp > order.expiryTime) {
            uint256 daysElapsed = (block.timestamp - order.expiryTime) / 86400;
            if (daysElapsed >= 100) redeemAmount = 0;
            else redeemAmount = ((100 - daysElapsed) * order.collateral) / 100;
        } else redeemAmount = order.collateral;

        makerBalances[order.maker] += order.collateral - redeemAmount;
        order.orderState = OrderState.Redeemed;
        emit OrderChange(order);
        _nft.permit(msg.sender, address(this), tokenId, deadline, 0, v, r, s);
        _nft.safeTransferFrom(msg.sender, order.maker, tokenId);
        payable(msg.sender).sendValue(redeemAmount);
    }

    /**
     * 出租方清算，收取全部押金，放弃NFT
     * 逾期12天后可强制清算
     * @param tokenId 放弃的NFT ID
     */
    function makerClear(uint256 tokenId) public {
        OrderInfo storage order = rentOrder[tokenId];
        require(order.maker == msg.sender, "not maker");
        require(order.orderState == OrderState.Borrowing, "NFT not borrowing");

        bool isClear = false;
        if (block.timestamp > order.expiryTime) {
            uint256 daysElapsed = (block.timestamp - order.expiryTime) / 86400;
            if (daysElapsed >= 12) {
                isClear = true;
            }
        }

        require(isClear, "Not allow clear");
        //require(makerBalances[order.maker] + order.collateral < type(uint256).max, "amount overflow");
        order.orderState = OrderState.MakerClear;
        uint256 sendBalances = makerBalances[order.maker] + order.collateral;
        require(sendBalances <= address(this).balance, "Insufficient balance to pay");
        makerBalances[order.maker] = 0;
        emit OrderChange(order);
        payable(msg.sender).sendValue(sendBalances);
    }

    /**
     * 出租方取款
     */
    function makerClaim() public {
        require(makerBalances[msg.sender] > 0, "No balances");
        require(makerBalances[msg.sender] <= address(this).balance, "Insufficient balance to pay");
        uint256 sendBalances = makerBalances[msg.sender];
        makerBalances[msg.sender] = 0;
        payable(msg.sender).sendValue(sendBalances);
    }
}
