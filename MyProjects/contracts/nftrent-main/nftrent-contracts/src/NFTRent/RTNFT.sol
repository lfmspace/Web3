// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

import "@openzeppelin/contracts/token/ERC721/ERC721.sol";
import "@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
import {ECDSA} from "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import {EIP712} from "@openzeppelin/contracts/utils/cryptography/EIP712.sol";
import {NoncesKeyed} from "@openzeppelin/contracts/utils/NoncesKeyed.sol";
import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";

contract RTNFT is ERC721, ERC721URIStorage, EIP712, NoncesKeyed, Ownable {
    uint256 tokenIdCounter = 0;
    //keccak256('Permit(address owner,address to,uint256 value,uint256 nonce,uint256 deadline,bytes32 msgHash)');
    bytes32 private constant PERMIT_TYPEHASH = 0x4ac553a37e01ec3c6bb3b436f31aa8101ceee19dbda551b523761ad60bad5146;

    error ERC2612InvalidSigner(address signer, address owner);
    error ERC2612ExpiredSignature(uint256 deadline);
    event NFTChange(address from, address to, uint256 tokenId, string nftUrl);

    constructor(address owner) ERC721("RTNFT", "RT") EIP712("RTNFT", "1") Ownable(owner) {}

    /**
     * 获取签名隔离域
     */
    function DOMAIN_SEPARATOR() external view virtual returns (bytes32) {
        return _domainSeparatorV4();
    }

    /**
     * 铸造NFT
     * @param to NFT接收地址
     * @param uri NFT元数据IPFS地址
     */
    function mintNFT(address to, string memory uri) public onlyOwner returns (uint256) {
        uint256 tokenId = ++tokenIdCounter;
        _setTokenURI(tokenId, uri);
        _safeMint(to, tokenId);
        return tokenId;
    }

    /**
     * 授权owner的tokenId可以被to地址转移
     * @param owner token拥有者
     * @param to 授权转移目的地址
     * @param tokenId 被授权tokenId
     * @param deadline 授权截止日期
     * @param msgHash 对特定消息哈希的授权，避免攻击方以纂改后的信息使用授权，由用户自行定义
     * @param v 签名V
     * @param r 签名r
     * @param s 签名s
     */
    function permit(address owner, address to, uint256 tokenId, uint256 deadline, bytes32 msgHash, uint8 v, bytes32 r, bytes32 s) public {
        //授权使用NoncesKeyed作为noces合约，不支持超过uint192的id，实际生产中如需要可自行开发支持uint256的NoncesKeyed
        require(tokenId < type(uint192).max, "Token only supports uint192");

        if (block.timestamp > deadline) {
            revert ERC2612ExpiredSignature(deadline);
        }

        uint256 n = _useNonce(owner, uint192(tokenId));
        bytes32 structHash = keccak256(abi.encode(PERMIT_TYPEHASH, owner, to, tokenId, n, deadline, msgHash));
        bytes32 hash = _hashTypedDataV4(structHash);
        address signer = ECDSA.recover(hash, v, r, s);
        if (signer != owner) {
            revert ERC2612InvalidSigner(signer, owner);
        }

        _approve(to, tokenId, signer);
    }

    /// @inheritdoc ERC721
    function supportsInterface(bytes4 interfaceId) public view override(ERC721, ERC721URIStorage) returns (bool) {
        return super.supportsInterface(interfaceId);
    }

    /// @inheritdoc ERC721
    function tokenURI(uint256 tokenId) public view override(ERC721, ERC721URIStorage) returns (string memory) {
        return super.tokenURI(tokenId);
    }

    /// @inheritdoc ERC721
    function _update(address to, uint256 tokenId, address auth) internal virtual override returns (address) {
        address oldOwner = _ownerOf(tokenId);
        address addr = super._update(to, tokenId, auth);
        emit NFTChange(oldOwner, to, tokenId, tokenURI(tokenId));
        return addr;
    }
}
