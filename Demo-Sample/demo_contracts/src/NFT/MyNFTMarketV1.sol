// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import './MyNFT.sol';
import '../Token/MyToken.sol';

import {ECDSA} from '@openzeppelin/contracts/utils/cryptography/ECDSA.sol';
import {Nonces} from '@openzeppelin/contracts/utils/Nonces.sol';
import '@openzeppelin/contracts/token/ERC721/IERC721Receiver.sol';
import '@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol';
import '@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol';
import '@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol';

import '@openzeppelin/contracts/utils/Strings.sol';

//forge install openzeppelin/openzeppelin-foundry-upgrades
//forge install openzeppelin/openzeppelin-contracts-upgradeable
contract MyNFTMarketV1 is
    IERC721Receiver,
    Nonces,
    Initializable,
    OwnableUpgradeable,
    UUPSUpgradeable
{
    uint256[50] private __gap; //预留存储槽位，避免后续父合约变量无法变更位置导致存储槽污染
    uint256 public cname;
    uint256 public num;
    MyNFT public _nft;
    MyToken public _token;
    mapping(uint256 => uint256) public _prices; //nft价格
    mapping(uint256 => address) public _owners; //nft拥有者
    mapping(address => uint) public _balances; //存钱列表

    error notOwner(uint256 tokenId, string msg);
    constructor() {
        _disableInitializers();
    }

    function initialize(
        address nftAddress,
        address tokenAddress,
        address initialOwner
    ) public reinitializer(1) {
        _nft = MyNFT(nftAddress);
        _token = MyToken(tokenAddress);
        __Ownable_init(initialOwner);
        __UUPSUpgradeable_init();
    }
    function _authorizeUpgrade(
        address newImplementation
    ) internal override onlyOwner {}

    function listUp(uint256 tokenId, uint256 amount) public returns (bool) {
        if (
            _nft.ownerOf(tokenId) != msg.sender &&
            _owners[tokenId] != msg.sender
        ) revert notOwner(tokenId, 'not owner');

        require(amount > 0, 'not allow amount 0');
        _prices[tokenId] = amount;
        _owners[tokenId] = msg.sender;
        _nft.safeTransferFrom(msg.sender, address(this), tokenId);
        return true;
    }

    //下架
    function listDown(uint256 tokenId) public returns (bool) {
        if (
            _nft.ownerOf(tokenId) != msg.sender &&
            _owners[tokenId] != msg.sender
        ) revert notOwner(tokenId, 'not owner');

        _prices[tokenId] = 0;
        _owners[tokenId] = address(0);
        _nft.safeTransferFrom(address(this), msg.sender, tokenId);
        return true;
    }
    event BalanceChange(address from, address to, uint256 amount);
    /**
    购买者转钱
    1.用户调用Token中的send方法
    2.合约中的send方法会调用该方法存款 
    */
    function TransferReceipt(
        address from,
        uint256 amount
    ) public returns (bool) {
        console.log('_balances[from]', amount);
        _balances[from] += amount;
        emit BalanceChange(from, msg.sender, amount);
        return true;
    }

    //购买NFT
    function buy(uint256 tokenId) public returns (bool) {
        require(_owners[tokenId] != address(0), 'nft upList');
        require(
            _prices[tokenId] <= _balances[msg.sender],
            'not enough amount '
        );
        _owners[tokenId] = address(0);
        _prices[tokenId] = 0;
        _balances[msg.sender] -= _prices[tokenId];
        _nft.safeTransferFrom(address(this), msg.sender, tokenId);
        return true;
    }

    function onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes calldata data
    ) external returns (bytes4) {
        _owners[tokenId] = operator;
        return IERC721Receiver.onERC721Received.selector;
    }
    function getcname() public view returns (uint256) {
        return cname;
    }

    function setcname() public returns (uint256) {
        cname = 1;
        //num = 2;
        return cname;
    }

    function increaseNum() public {
        num++;
    }
}
