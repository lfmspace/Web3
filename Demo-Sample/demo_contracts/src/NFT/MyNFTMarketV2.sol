// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import './MyNFT.sol';
import '../Token/MyToken.sol';

import {ECDSA} from '@openzeppelin/contracts/utils/cryptography/ECDSA.sol';
import {EIP712} from '@openzeppelin/contracts/utils/cryptography/EIP712.sol';
import {
    ShortStrings,
    ShortString
} from '@openzeppelin/contracts/utils/ShortStrings.sol';
import {Nonces} from '@openzeppelin/contracts/utils/Nonces.sol';
import '@openzeppelin/contracts/token/ERC721/IERC721Receiver.sol';
import '@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol';
import '@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol';
import '@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol';

contract MyNFTMarketV2 is
    IERC721Receiver,
    Nonces,
    Initializable,
    OwnableUpgradeable,
    UUPSUpgradeable,
    EIP712
{
    uint256[48] private __gap;
    uint256 public cname;
    uint256 public num;
    MyNFT public _nft;
    MyToken public _token;
    mapping(uint256 => uint256) public _prices; //nft价格
    mapping(uint256 => address) public _owners; //nft拥有者
    mapping(address => uint) public _balances; //存钱列表
    bytes32 private constant PERMIT_TYPEHASH_buyer =
        keccak256('Permit(address buyer,uint256 nonce,uint256 deadline)');
    error ERC2612InvalidSigner(address signer, address owner);
    error ERC2612ExpiredSignature(uint256 deadline);
    error notOwner(uint256 tokenId, string msg);
    ShortString private _name;
    ShortString private _version;
    string private _nameFallback;
    string private _versionFallback;
    using ShortStrings for *;
    uint256 public cname2;
    constructor(
        address nftAddress,
        address tokenAddress
    ) EIP712('MyNFTMarket', '1') {
        _disableInitializers();
    }

    function initialize(
        string memory name712,
        string memory version712
    ) public reinitializer(2) {
        _name = name712.toShortStringWithFallback(_nameFallback);
        _version = version712.toShortStringWithFallback(_versionFallback);
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

    //签名上架
    function permitList(
        uint256 tokenId,
        uint256 amount,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) public returns (bool) {
        if (
            _nft.ownerOf(tokenId) != msg.sender &&
            _owners[tokenId] != msg.sender
        ) revert notOwner(tokenId, 'not owner');

        //_owners[tokenId] = msg.sender; //to onERC721Received
        _prices[tokenId] = amount;
        _nft.permit(msg.sender, address(this), tokenId, deadline, v, r, s);
        //if (amount > 0) revert ss(_nft.getApproved(tokenId));
        _nft.safeTransferFrom(msg.sender, address(this), tokenId);
        return true;
    }

    //合约授权的用户才可以购买NFT
    function permitBuy(
        uint256 tokenId,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) public returns (bool) {
        if (block.timestamp > deadline) {
            revert ERC2612ExpiredSignature(deadline);
        }
        bytes32 structHash = keccak256(
            abi.encode(
                PERMIT_TYPEHASH_buyer,
                msg.sender,
                _useNonce(msg.sender),
                deadline
            )
        );

        bytes32 hash = _hashTypedDataV4(structHash);

        address signer = ECDSA.recover(hash, v, r, s);
        if (signer != owner()) {
            revert ERC2612InvalidSigner(signer, owner());
        }

        require(_owners[tokenId] != address(0), 'nft upList');
        console.log('_prices[tokenId]', _prices[tokenId]);
        console.log('_balances[msg.sender]', _balances[msg.sender]);
        require(_prices[tokenId] <= _balances[msg.sender], 'not enough amount');
        _owners[tokenId] = address(0);
        _prices[tokenId] = 0;
        _balances[msg.sender] -= _prices[tokenId];
        _nft.safeTransferFrom(address(this), msg.sender, tokenId);
        return true;
    }

    function DOMAIN_SEPARATOR() external view returns (bytes32) {
        return _domainSeparatorV4();
    }
}
