//SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;
import "@openzeppelin/contracts/token/ERC721/ERC721.sol";
import "@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
//import "./node_modules/@openzeppelin/contracts/utils/Counters.sol";


/*
发⾏⼀个 ERC721 Token（⽤⾃⼰的名字）
• 铸造⼏个 NFT，在测试⽹上发⾏，在 Opensea 上查看
• 编写⼀个市场合约 NFTMarket：使⽤⾃⼰发⾏的 ERC20 Token 来买 NFT： • NFT 持有者可上架 NFT（list() 设置价格 多少个 TOKEN 购买 NFT ） • 编写购买NFT ⽅法 buyNFT(uint tokenID, uint amount)，转⼊对应的TOKEN，获取对应的 NFT
• MyToken : transferWithCallback(address to, uint amount, bytes32 data) {
• To.tokenReceived(msg.sender, to, amount, data). // erc721 token;
https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafkreiagib35wsyi5wpimd6knydcj4hw4qhohemhx6sglpclwlhtutcuq4
*/

contract LNFT721 is ERC721,ERC721URIStorage{
  

 constructor() ERC721("LFMNFT","LNFT"){}
   uint256 id=0;
   function mint(address _owner,string memory url) public{
      _mint(_owner,id);
      _setTokenURI(id,url);
      id++;
   }

 function tokenURI(uint256 tokenId) public  view override(ERC721,ERC721URIStorage) returns(string memory){
   return super.tokenURI(tokenId);
 }
  function supportsInterface(bytes4 interfaceId)public view override(ERC721,ERC721URIStorage) returns(bool){
  return super.supportsInterface(interfaceId);
  }

 }    
  
