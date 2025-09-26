// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import "@openzeppelin/contracts/proxy/Clones.sol";
import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {Ownable} from "@openzeppelin/contracts/access/Ownable.sol";
import {ReentrancyGuard} from "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import {IUniswapV2Factory} from "@uniswap/v2-core/interfaces/IUniswapV2Factory.sol";
import {IUniswapV2Router02} from "@uniswap/v2-periphery/interfaces/IUniswapV2Router02.sol";
import "./Meme.sol";
import "./BondingCurve.sol";

contract MemeFactory is ReentrancyGuard, Ownable {
    uint256 public FUNDING_GLOBAL = 50 ether; //meme需要募集的资金总数
    uint256 public constant MAX_SUPPLY = 10 ** 9 * 1 ether;
    uint256 public constant LIQUIDE_SUPPLY = (MAX_SUPPLY * 1) / 5; //添加流动性初始量
    uint256 public constant FUNDING_SUPPLY = (MAX_SUPPLY * 4) / 5; //募集提供量
    address public immutable memeImplement;
    address public immutable uniswapV2Router;
    address public immutable uniswapV2Factory;
    BondingCurve public immutable bondingCurve;
    mapping(address => TokenState) public tokenStates;
    mapping(address => uint256) public tokenFund;

    enum TokenState {
        NOTCREATE,
        FUNDING,
        TRADING
    }

    event MemeCreate(address token);
    event LiquidePoolCreate(address pair);

    constructor(address _logic, address _uniswapV2Router, address _uniswapV2Factory, uint256 curve_param_a, uint256 curve_param_b) Ownable(msg.sender) {
        memeImplement = _logic;
        uniswapV2Router = _uniswapV2Router;
        uniswapV2Factory = _uniswapV2Factory;
        bondingCurve = new BondingCurve(curve_param_a, curve_param_b);
    }

    function createToken(string memory name, string memory symbol) external returns (address) {
        address proxy = Clones.clone(memeImplement);
        Meme(proxy).init(name, symbol);
        tokenStates[proxy] = TokenState.FUNDING;
        emit MemeCreate(proxy);
        return proxy;
    }

    function buy(address token) external payable nonReentrant {
        //判断token合法
        require(tokenStates[token] == TokenState.FUNDING, "Token not found");
        //限制最小申购额度
        require(msg.value > 0.01 ether, "Too little money");

        uint256 globalLack = FUNDING_GLOBAL - tokenFund[token];
        uint256 allowBuyEth = msg.value > globalLack ? globalLack : msg.value;
        uint256 returnBuyEth = msg.value - allowBuyEth;
        Meme meme = Meme(token);
        //计算购买token数额
        uint256 tokenAmount = bondingCurve.calculateSell(meme.totalSupply(), allowBuyEth);

        uint256 totalFund = tokenFund[token];
        //汇总token募集总金额
        totalFund += allowBuyEth;

        meme.mint(token, tokenAmount);
        //判断是否募集足够
        //募集足够添加流动性
        if (tokenFund[token] >= FUNDING_GLOBAL) {
            meme.mint(token, LIQUIDE_SUPPLY);
            //创建交易池
            address pair = createLiquidityPool(token);

            tokenStates[token] = TokenState.TRADING;
            //添加流动性
            uint256 liquide = addLiquidity(token, LIQUIDE_SUPPLY, totalFund);
            totalFund = 0;

            //销毁初始流动性，避免池子被清空，避免膨胀攻击
            SafeERC20.safeTransfer(IERC20(pair), address(0), liquide);

            emit LiquidePoolCreate(pair);
        }
        tokenFund[token] = totalFund;
        if (returnBuyEth > 0) {
            (bool success, ) = msg.sender.call{value: returnBuyEth}("");
            require(success, "Return exceed fail");
        }
    }

    function sell(address token, uint256 amount) external nonReentrant {
        //判断Token合法性
        require(tokenStates[token] == TokenState.FUNDING, "Token not found");
        Meme meme = Meme(token);

        //判断数量合法性
        require(amount > 0, "Amount must greater 0");
        require(meme.balanceOf(msg.sender) >= amount, "Token not enough");

        //计算所得eth金额
        uint256 ethAmount = bondingCurve.calculateSell(meme.totalSupply(), amount);

        //修改状态&打款
        tokenFund[token] -= ethAmount;
        meme.burn(msg.sender, amount);
        (bool success, ) = msg.sender.call{value: ethAmount}("");
        require(success, "ETH send fail");
    }

    function createLiquidityPool(address token) internal returns (address pair) {
        IUniswapV2Factory factory = IUniswapV2Factory(uniswapV2Factory);
        IUniswapV2Router02 router = IUniswapV2Router02(uniswapV2Router);
        pair = factory.createPair(token, router.WETH());
    }

    function addLiquidity(address token, uint256 tokenAmount, uint256 ethAmount) internal returns (uint256) {
        IUniswapV2Router02 router = IUniswapV2Router02(uniswapV2Router);
        Meme(token).approve(uniswapV2Router, tokenAmount);
        (, , uint256 liquidity) = router.addLiquidityETH{value: ethAmount}(token, tokenAmount, tokenAmount, ethAmount, address(this), block.timestamp);
        return liquidity;
    }
}
