pragma solidity 0.8.25;

import '@openzeppelin/contracts/token/ERC20/ERC20.sol';
import '@openzeppelin/contracts/proxy/utils/Initializable.sol';
import {Ownable} from '@openzeppelin/contracts/access/Ownable.sol';
import {Test, console} from 'forge-std/Test.sol';

contract Meme is ERC20, Initializable, Ownable {
    string _symbol;
    uint256 _totalSupply;
    uint _perMint;
    uint _fee;
    address _os;
    address _owner;
    uint256 currentCounters; //记录铸造总数
    constructor(address owner) ERC20('Meme', 'me') Ownable(owner) {
        _disableInitializers(); //确保初始化只运行一次
    }

    function init(
        string memory symbol,
        uint256 totalSupply,
        uint256 perMint,
        uint256 price,
        address os,
        address owner
    ) public initializer {
        console.log('init perMint is', perMint);
        _symbol = symbol;
        _totalSupply = totalSupply;
        _perMint = perMint;
        _fee = price * perMint;
        _os = os;
        _owner = owner;
    }

    error NoEnoughAmount(address from, address to, uint256 amount);
    error MoreAmount(address from, address to, uint256 amount);
    error ApplyEnded(address from);
    function mintMeme() public payable {
        if (msg.value > _fee) {
            revert MoreAmount(msg.sender, address(this), msg.value);
        }
        if (msg.value < _fee) {
            revert NoEnoughAmount(msg.sender, address(this), msg.value);
        }
        if (currentCounters + _perMint > _totalSupply) {
            revert ApplyEnded(address(this));
        }
        (bool osSuccess, ) = payable(address(_os)).call{
            value: (msg.value * 1) / 100
        }('');
        (bool ownerSuccess, ) = payable(address(_owner)).call{
            value: (msg.value * 99) / 100
        }('');
        if (!osSuccess || !ownerSuccess) revert('pable fail');
        super._mint(msg.sender, _perMint);
    }
}
