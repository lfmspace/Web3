// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import '@openzeppelin/contracts/token/ERC721/ERC721.sol';
import '@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol';
import {ECDSA} from '@openzeppelin/contracts/utils/cryptography/ECDSA.sol';
import {EIP712} from '@openzeppelin/contracts/utils/cryptography/EIP712.sol';
import {Nonces} from '@openzeppelin/contracts/utils/Nonces.sol';
import {Ownable} from '@openzeppelin/contracts/access/Ownable.sol';
import {Test, console} from 'forge-std/Test.sol';

contract MyNFT is ERC721, ERC721URIStorage, EIP712, Nonces, Ownable {
    bytes32 private constant PERMIT_TYPEHASH =
        keccak256(
            'Permit(address owner,address to,uint256 tokenId,uint256 nonce,uint256 deadline)'
        );

    error ERC2612InvalidSigner(address signer, address owner);
    error ERC2612ExpiredSignature(uint256 deadline);
    uint256 tokenIdCounter = 0;

    constructor(
        address owner
    ) ERC721('MyNFT', 'NFT') EIP712('MyNFT', '1') Nonces() Ownable(owner) {}

    function tokenURI(
        uint256 tokenId
    ) public view override(ERC721, ERC721URIStorage) returns (string memory) {
        return super.tokenURI(tokenId);
    }

    function DOMAIN_SEPARATOR() external view virtual returns (bytes32) {
        return _domainSeparatorV4();
    }

    function supportsInterface(
        bytes4 interfaceId
    ) public view override(ERC721, ERC721URIStorage) returns (bool) {
        return super.supportsInterface(interfaceId);
    }
    function mintNFT(
        address to,
        string memory uri
    ) public onlyOwner returns (uint256) {
        uint256 tokenId = tokenIdCounter++;
        _safeMint(to, tokenId);
        _setTokenURI(tokenId, uri);
        return tokenId;
    }

    function permit(
        address owner,
        address to,
        uint256 tokenId,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) public virtual {
        if (block.timestamp > deadline) {
            revert ERC2612ExpiredSignature(deadline);
        }

        bytes32 structHash = keccak256(
            abi.encode(
                PERMIT_TYPEHASH,
                owner,
                to,
                tokenId,
                _useNonce(owner),
                deadline
            )
        );
        bytes32 hash = _hashTypedDataV4(structHash);
        address signer = ECDSA.recover(hash, v, r, s);
        if (signer != owner) {
            revert ERC2612InvalidSigner(signer, owner);
        }

        _approve(to, tokenId, signer);
    }
}
