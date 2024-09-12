pragma solidity ^0.8.4;

// SPDX-License-Identifier: Unlicensed

abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return payable(msg.sender);
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    constructor() {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    function owner() public view returns (address) {
        return _owner;
    }

    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

abstract contract ReentrancyGuard {
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}

library SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold
        return c;
    }

    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

interface IERC20 {
    function totalSupply() external view returns (uint256);

    function balanceOf(address account) external view returns (uint256);

    function transfer(address recipient, uint256 amount)
        external
        returns (bool);

    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

interface IProviderPair {
    function getReserves()
        external
        view
        returns (
            uint112,
            uint112,
            uint32
        );

    function token0() external view returns (address);

    function token1() external view returns (address);
}

contract TabooPresale is ReentrancyGuard, Ownable {
    using SafeMath for uint256;

    IERC20 public _token = IERC20(0x9abDbA20EdFbA06B782126b4D8d72A5853918FD0);
    IERC20 public _WBNB = IERC20(0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c);
    IERC20 public _BUSD = IERC20(0xe9e7CEA3DedcA5984780Bafc599bD69ADd087D56);
    IERC20 public _ETH = IERC20(0x2170Ed0880ac9A755fd29B2688956BD959F933F8);
    IERC20 public _MATIC = IERC20(0xCC42724C6683B7E57334c4E856f4c9965ED682bD);
    IERC20 public _BTC = IERC20(0x7130d2A12B9BCbFAe4f2634d864A1Ee1Ce3Ead9c);
    IERC20 public _ADA = IERC20(0x3EE2200Efb3400fAbB9AacF31297cBdD1d435D47);
    IERC20 public _DOGE = IERC20(0xbA2aE424d960c26247Dd6c32edC70B295c744C43);
    IERC20 public _CHAINLINK =
        IERC20(0xF8A0BF9cF54Bb92F17374d9e9A321E6a111a51bD);
    IERC20 public _USDC = IERC20(0x8AC76a51cc950d9822D68b83fE1Ad97B32Cd580d);
    IERC20 public _USDT = IERC20(0x55d398326f99059fF775485246999027B3197955);
    IERC20 public _UNI = IERC20(0xBf5140A22578168FD562DCcF235E5D43A02ce9B1);

    IProviderPair TokenBnb =
        IProviderPair(0xb4E7b227D344c8BA1604Ae241898E02dA3d1Fe63);
    IProviderPair BusdBnb =
        IProviderPair(0xDc558D64c29721d74C4456CfB4363a6e6660A9Bb);
    IProviderPair BusdEth =
        IProviderPair(0x7213a321F1855CF1779f42c0CD85d3D95291D34C);
    IProviderPair BnbMatic =
        IProviderPair(0x3B09e13Ca9189FBD6a196cfE5FbD477C885afBf3);
    IProviderPair BusdBtc =
        IProviderPair(0xF45cd219aEF8618A92BAa7aD848364a158a24F33);
    IProviderPair BusdAda =
        IProviderPair(0x1E249DF2F58cBef7EAc2b0EE35964ED8311D5623);
    IProviderPair BusdDoge =
        IProviderPair(0xE27859308ae2424506D1ac7BF5bcb92D6a73e211);
    IProviderPair BnbChain =
        IProviderPair(0x16Fe21c91c426E603977b1C6EcD59Fc510a518C2);
    IProviderPair BnbUni =
        IProviderPair(0x014608E87AF97a054C9a49f81E1473076D51d9a3);

    address payable public _wallet;
    address payable public _outGoingWallet;
    uint256 public _minAmount;

    bool public paused;

    event Pausable(bool state);

    event TokensPurchased(
        address purchaser,
        address beneficiary,
        uint256 value,
        uint256 amount
    );

    modifier whenNotPaused() {
        require(!paused, "contract paused");
        _;
    }

    constructor(
        address payable wallet,
        address payable outGoingWallet,
        uint256 minAmount
    ) {
        require(wallet != address(0), "Pre-Sale: wallet is the zero address");
        require(
            outGoingWallet != address(0),
            "Pre-Sale: wallet is the zero address"
        );
        _wallet = wallet;
        _outGoingWallet = outGoingWallet;
        _minAmount = minAmount;
    }

    receive() external payable {
        // React to receiving ether
    }

    function setProvider(
        IProviderPair _TokenBnb,
        IProviderPair _BusdBnb,
        IProviderPair _BusdEth,
        IProviderPair _BusdBtc,
        IProviderPair _BnbMatic,
        IProviderPair _BusdAda,
        IProviderPair _BusdDoge,
        IProviderPair _BnbChain,
        IProviderPair _BnbUni
    ) external onlyOwner {
        TokenBnb = _TokenBnb;
        BusdBnb = _BusdBnb;
        BusdEth = _BusdEth;
        BusdBtc = _BusdBtc;
        BnbMatic = _BnbMatic;
        BusdAda = _BusdAda;
        BusdDoge = _BusdDoge;
        BnbChain = _BnbChain;
        BnbUni = _BnbUni;
    }

    //Pre-Sale
    function buyTokensBNB(address _beneficiary) public payable nonReentrant whenNotPaused {
        uint256 bnbAmount = msg.value;
        (bool success, ) = payable(_wallet).call{value: bnbAmount}("");
        require(success);
        uint256 tokens = _getTokenAmount(bnbAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, bnbAmount, tokens);
    }

    function buyTokensBUSD(address _beneficiary, uint256 _BUSDAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _BUSD.transferFrom(msg.sender, _wallet, _BUSDAmount);
        uint256 tokens = _getTokenAmountBUSD(_BUSDAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _BUSDAmount, tokens);
    }

    function buyTokensUSDC(address _beneficiary, uint256 _USDCAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _USDC.transferFrom(msg.sender, _wallet, _USDCAmount);
        uint256 tokens = _getTokenAmountUSDC(_USDCAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _USDCAmount, tokens);
    }

    function buyTokensUSDT(address _beneficiary, uint256 _USDTAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _USDT.transferFrom(msg.sender, _wallet, _USDTAmount);
        uint256 tokens = _getTokenAmountUSDT(_USDTAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _USDTAmount, tokens);
    }

    function buyTokensETH(address _beneficiary, uint256 _ETHAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _ETH.transferFrom(msg.sender, _wallet, _ETHAmount);
        uint256 tokens = _getTokenAmountETH(_ETHAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _ETHAmount, tokens);
    }

    function buyTokensBTC(address _beneficiary, uint256 _BTCAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _BTC.transferFrom(msg.sender, _wallet, _BTCAmount);
        uint256 tokens = _getTokenAmountBTC(_BTCAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _BTCAmount, tokens);
    }

    function buyTokensMATIC(address _beneficiary, uint256 _MATICAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _MATIC.transferFrom(msg.sender, _wallet, _MATICAmount);
        uint256 tokens = _getTokenAmountMATIC(_MATICAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _MATICAmount, tokens);
    }

    function buyTokensADA(address _beneficiary, uint256 _ADAAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _ADA.transferFrom(msg.sender, _wallet, _ADAAmount);
        uint256 tokens = _getTokenAmountADA(_ADAAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _ADAAmount, tokens);
    }

    function buyTokensDOGE(address _beneficiary, uint256 _DOGEAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _DOGE.transferFrom(msg.sender, _wallet, _DOGEAmount);
        uint256 tokens = _getTokenAmountDOGE(_DOGEAmount * (10**10));
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _DOGEAmount, tokens);
    }

    function buyTokensCHAIN(address _beneficiary, uint256 _CHAINAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _CHAINLINK.transferFrom(msg.sender, _wallet, _CHAINAmount);
        uint256 tokens = _getTokenAmountCHAIN(_CHAINAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _CHAINAmount, tokens);
    }

    function buyTokensUNI(address _beneficiary, uint256 _UNIAmount)
        public
        nonReentrant
        whenNotPaused
    {
        _UNI.transferFrom(msg.sender, _wallet, _UNIAmount);
        uint256 tokens = _getTokenAmountUNI(_UNIAmount);
        require(tokens >= _minAmount,"Please buy tokens above the minimum limit");
        _token.transferFrom(_outGoingWallet, _beneficiary, tokens);
        emit TokensPurchased(_msgSender(), _beneficiary, _UNIAmount, tokens);
    }

    function withdrawBNB() external onlyOwner {
        (bool success, ) = payable(_wallet).call{value: address(this).balance}(
            ""
        );
        require(success);
    }

    function setAddress(
        IERC20 token,
        IERC20 busd,
        IERC20 eth,
        IERC20 btc,
        IERC20 matic,
        IERC20 ada,
        IERC20 doge,
        IERC20 chainLink,
        IERC20 uni,
        IERC20 usdc,
        IERC20 usdt
    ) external onlyOwner {
        _BUSD = busd;
        _ETH = eth;
        _BTC = btc;
        _MATIC = matic;
        _ADA = ada;
        _DOGE = doge;
        _CHAINLINK = chainLink;
        _UNI = uni;
        _USDC = usdc;
        _USDT = usdt;
        _token = token;
    }

    function pause(bool _state) external nonReentrant onlyOwner {
        paused = _state;
        emit Pausable(_state);
    }

    function setToken(IERC20 token) external onlyOwner {
        _token = token;
    }

    function setMinAmount(uint256 minAmount) external onlyOwner {
        _minAmount = minAmount;
    }

    function setAdminWallet(
        address payable incommingWallet,
        address payable outGoingWallet
    ) external onlyOwner {
        _wallet = incommingWallet;
        _outGoingWallet = outGoingWallet;
    }

    function takeTokens(IERC20 _TokenAddress) public onlyOwner {
        IERC20 tokenBEP = _TokenAddress;
        uint256 tokenAmt = tokenBEP.balanceOf(address(this));
        require(tokenAmt > 0, "BEP-20 balance is 0");
        tokenBEP.transfer(_wallet, tokenAmt);
    }

    function _getTokenAmount(uint256 _bnbAmount)
        internal
        view
        returns (uint256)
    {
        return _bnbAmount.mul(bnbRate()).div(10**18);
    }

    function _getTokenAmountBUSD(uint256 _busdAmount)
        internal
        view
        returns (uint256)
    {
        return _busdAmount.mul(getTabooPrice()).div(10**18);
    }

    function _getTokenAmountETH(uint256 _ethAmount)
        internal
        view
        returns (uint256)
    {
        return _ethAmount.mul(ethRate()).div(10**18);
    }

    function _getTokenAmountBTC(uint256 _btcAmount)
        internal
        view
        returns (uint256)
    {
        return _btcAmount.mul(btcRate()).div(10**18);
    }

    function _getTokenAmountMATIC(uint256 _maticAmount)
        internal
        view
        returns (uint256)
    {
        return _maticAmount.mul(maticRate()).div(10**18);
    }

    function _getTokenAmountDOGE(uint256 _dogeAmount)
        internal
        view
        returns (uint256)
    {
        return _dogeAmount.mul(dogeRate()).div(10**18);
    }

    function _getTokenAmountADA(uint256 _adaAmount)
        internal
        view
        returns (uint256)
    {
        return _adaAmount.mul(adaRate()).div(10**18);
    }

    function _getTokenAmountCHAIN(uint256 _chainAmount)
        internal
        view
        returns (uint256)
    {
        return _chainAmount.mul(chainRate()).div(10**18);
    }

    function _getTokenAmountUNI(uint256 _uniAmount)
        internal
        view
        returns (uint256)
    {
        return _uniAmount.mul(uniRate()).div(10**18);
    }

    function _getTokenAmountUSDC(uint256 _usdcAmount)
        internal
        view
        returns (uint256)
    {
        return _usdcAmount.mul(getTabooPrice()).div(10**18);
    }

    function _getTokenAmountUSDT(uint256 _usdtAmount)
        internal
        view
        returns (uint256)
    {
        return _usdtAmount.mul(getTabooPrice()).div(10**18);
    }

    function getPriceData(IProviderPair _pairAddress)
        public
        view
        returns (uint256)
    {
        uint112 reserve0;
        uint112 reserve1;
        uint32 timestamp;
        uint256 exchangeRate;
        (reserve0, reserve1, timestamp) = IProviderPair(_pairAddress)
            .getReserves();
        address token0 = IProviderPair(_pairAddress).token0();
        if (token0 == address(_BUSD)) {
            exchangeRate = (uint256((uint256(reserve0) * (10**9)) / uint256(reserve1)));
        } else {
            exchangeRate = (uint256((uint256(reserve1) * (10**9)) / uint256(reserve0)));
        }
        return (exchangeRate);
    }

    function getPriceDataBnb(IProviderPair _pairAddress)
        public
        view
        returns (uint256)
    {
        uint112 reserve0;
        uint112 reserve1;
        uint32 timestamp;
        uint256 exchangeRate;
        (reserve0, reserve1, timestamp) = IProviderPair(_pairAddress)
            .getReserves();
        address token0 = IProviderPair(_pairAddress).token0();
        if (token0 == address(_WBNB)) {
            exchangeRate = (uint256((uint256(reserve0) * (10**9)) / uint256(reserve1)));
        } else {
            exchangeRate = (uint256((uint256(reserve1) * (10**9)) / uint256(reserve0)));
        }
        return (exchangeRate);
    }

    function getTabooPrice() public view returns (uint256) {
        uint112 reserve0;
        uint112 reserve1;
        uint32 timestamp;
        uint256 exchangeRate;
        (reserve0, reserve1, timestamp) = IProviderPair(TokenBnb).getReserves();
        address token0 = IProviderPair(TokenBnb).token0();
        if (token0 == address(_token)) {
            exchangeRate = (uint256((uint256(reserve0) * (10**18)) / uint256(reserve1)));
        } else {
            exchangeRate = (uint256((uint256(reserve1) * (10**18)) / uint256(reserve0)));
        }
        uint256 bnbPrice = getPriceData(BusdBnb);
        exchangeRate = (exchangeRate * 1e9) / bnbPrice;
        return (exchangeRate);
    }

    function bnbRate() public view returns (uint256) {
        uint256 bnbrate = (getPriceData(BusdBnb).mul(getTabooPrice())).div(
            10**9
        );
        return (bnbrate);
    }

    function ethRate() public view returns (uint256) {
        uint256 ethrate = (getPriceData(BusdEth).mul(getTabooPrice())).div(
            10**9
        );
        return (ethrate);
    }

    function btcRate() public view returns (uint256) {
        uint256 btcrate = (getPriceData(BusdBtc).mul(getTabooPrice())).div(
            10**9
        );
        return (btcrate);
    }

    function maticRate() public view returns (uint256) {
        uint256 maticrate = (
            getPriceDataBnb(BnbMatic).mul(getPriceData(BusdBnb)).mul(
                getTabooPrice()
            )
        ).div(10**18);
        return (maticrate);
    }

    function adaRate() public view returns (uint256) {
        uint256 adarate = (getPriceData(BusdAda).mul(getTabooPrice())).div(
            10**9
        );
        return (adarate);
    }

    function dogeRate() public view returns (uint256) {
        uint256 dogerate = (
            (getPriceData(BusdDoge).div(10**10)).mul(getTabooPrice())
        ).div(10**9);
        return (dogerate);
    }

    function chainRate() public view returns (uint256) {
        uint256 chainlinkrate = (
            getPriceDataBnb(BnbChain).mul(getPriceData(BusdBnb)).mul(
                getTabooPrice()
            )
        ).div(10**18);
        return (chainlinkrate);
    }

    function uniRate() public view returns (uint256) {
        uint256 unirate = (
            getPriceDataBnb(BnbUni).mul(getPriceData(BusdBnb)).mul(
                getTabooPrice()
            )
        ).div(10**18);
        return (unirate);
    }
}