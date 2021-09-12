// SPDX-License-Identifier: MIT

//Website : www.pumpkins.farm
//Telegram : https://t.me/pumpkinsfarmftm


pragma solidity ^0.6.12;


abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

contract PumpKinsFarm is Context, IERC20, Ownable {
    using SafeMath for uint256;
    using Address for address;

    mapping(address => uint256) private _balances;
    mapping (address => mapping (address => uint256)) private _allowances;
    
    mapping (address => bool) private _isExcludedFromFee;

    
    string  private constant _NAME = "PUMPKINS";
    string  private constant _SYMBOL = "KINS";
    uint8   private constant _DECIMALS = 18;
   
    uint256 private constant _DECIMALFACTOR = 10 ** uint256(_DECIMALS);

    
    uint256 private _tTotal = 26000 * _DECIMALFACTOR;
    uint256 private _totalSupply;
    
    uint256 private _tFeeTotal;
    uint256 private _tBurnTotal;
    

    uint256 public     _BURN_FEE = 20;
    uint256 public     _FARM_FEE = 50;
    uint256 public      _ILP_FEE = 10;    
    uint256 public      _DEV_FEE = 10;
    uint256 public      _MARKETING_FEE = 10;
    uint256 public  _MAX_TX_SIZE = 26000 * _DECIMALFACTOR;
    
    address public WDev;
    address public WFarm;
    address public WKinsIlp;
    address public WKinsmaster;
    address public WMarketing;
    address public operator;
    bool public TakeFee;
    
    event NewDeveloper(address);
    event ExcludeFromFee(address);	
    event IncludeInFee(address);
    event BurnFeeUpdated(uint256,uint256);
    event IlpFeeUpdated(uint256,uint256);
    event DevFeeUpdated(uint256,uint256);
    event FarmFeeUpdated(uint256,uint256);
    event MarketingFeeUpdated(uint256,uint256);
    
    modifier onlyDev() {
        require(msg.sender == owner() || msg.sender == operator , "Error: Require developer or Owner");
        _;
    }
    
    

    constructor (address _WDev, address _WMarketing, address _operator, bool _takeFee)
        public {
        _totalSupply = _tTotal;
        _balances[msg.sender] = _tTotal;
        
        
        WDev = _WDev;
        WMarketing = _WMarketing;
        operator = _operator;
        TakeFee = _takeFee;
        //exclude farm_vault , IlpVault & Owner from fee	
        _isExcludedFromFee[msg.sender] = true;
        _isExcludedFromFee[_WMarketing] = true;
        emit Transfer(address(0), _msgSender(), _tTotal);
    }

    function name() public pure returns (string memory) {
        return _NAME;
    }

    function symbol() public pure returns (string memory) {
        return _SYMBOL;
    }

    function decimals() public pure returns (uint8) {
        return _DECIMALS;
    }

    function totalSupply() public view override returns (uint256) {
        return _totalSupply;
    }

    function balanceOf(address account) public view override returns (uint256) {

        return (_balances[account]);
    }

    function transfer(address recipient, uint256 amount) public override returns (bool) {
        _kinstransfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender) public view override returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount) public override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(address sender, address recipient, uint256 amount) public override returns (bool) {
        _kinstransfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        return true;
    }

    
    function setWKinsIlp(address _WKinsIlp)public onlyDev returns (bool){
        WKinsIlp = _WKinsIlp;
        _isExcludedFromFee[_WKinsIlp] = true;
         return true;
    }

    function setWKinsmaster(address _kinsmaster)public onlyDev returns (bool){
        WKinsmaster = _kinsmaster;
        _isExcludedFromFee[_kinsmaster] = true;
         return true;
    }
    
    function setWMarketing(address _wmarketing)public onlyDev returns (bool){
        WMarketing = _wmarketing;
        _isExcludedFromFee[_wmarketing] = true;
         return true;
    }
    
    function setWFarm(address _wfarm)public onlyDev returns (bool){
        WFarm = _wfarm;
        _isExcludedFromFee[_wfarm] = true;
         return true;
    }
    
    function setDev(address _Wdev) external onlyDev {
        WDev = _Wdev ;
        _isExcludedFromFee[_Wdev] = true;
        emit NewDeveloper(_Wdev);
    }
    
    function setOperator(address _operator) external onlyDev {
        operator = _operator ;
        _isExcludedFromFee[_operator] = true;
        emit NewDeveloper(_operator);
    }
    
    function setTakeFee(bool _takefee)public onlyDev returns (bool){
        TakeFee = _takefee;
         return true;
    }
    
    function setFarmFee(uint256 farmFee) external onlyDev() {	
        require(farmFee <= 100 , "Error : MaxFarmFee is 10%");
        uint256 _previousFarmFee = _FARM_FEE;	
        _FARM_FEE = farmFee;	
        emit BurnFeeUpdated(_previousFarmFee,_FARM_FEE);	
    }
    
    function setBurnFee(uint256 burnFee) external onlyDev() {	
        require(burnFee <= 50 , "Error : MaxBurnFee is 5%");
        uint256 _previousBurnFee = _BURN_FEE;	
        _BURN_FEE = burnFee;	
        emit BurnFeeUpdated(_previousBurnFee,_BURN_FEE);	
    }	
    	
    function setDevFee(uint256 devFee) external onlyDev() {	
        require(devFee <= 20 , "Error : MaxDevFee is 2%");
        uint256 _previousDevFee = _DEV_FEE;	
        _DEV_FEE = devFee;	
        	
        emit DevFeeUpdated(_previousDevFee,_DEV_FEE);	
    }
    
    function setMarketingFee(uint256 marketingFee) external onlyDev() {	
        require(marketingFee <= 20 , "Error : MaxMarketingFee is 2%");
        uint256 _previousMarketingFee = _MARKETING_FEE;	
        _MARKETING_FEE = marketingFee;	
        	
        emit DevFeeUpdated(_previousMarketingFee,_DEV_FEE);	
    }
    
    function setIlpFee(uint256 ilpFee) external onlyDev() {	
        require(ilpFee <= 20 , "Error : MaxIlpFee is 2%");
        uint256 _previousIlpFee = _ILP_FEE;	
        _ILP_FEE = ilpFee;	
        	
        emit IlpFeeUpdated(_previousIlpFee,_ILP_FEE);	
    }
    
    function setMaxTxPercent(uint256 maxTxPercent) external onlyDev() {
        require(maxTxPercent >= 5 , "Error : Minimum maxTxLimit is 5%");
        require(maxTxPercent <= 100 , "Error : Maximum maxTxLimit is 100%");
        _MAX_TX_SIZE = totalSupply().mul(maxTxPercent).div(	
            10**2	
        );	
    }

    function excludeFromFee(address account) external onlyOwner {
        require(!_isExcludedFromFee[account], "Account is already excluded From Fee");
        _isExcludedFromFee[account] = true;	
        emit ExcludeFromFee(account);	
    }	
    	
    	
    function includeInFee(address account) external onlyOwner {	
         require( _isExcludedFromFee[account], "Account is not excluded From Fee");	
        _isExcludedFromFee[account] = false;	
        emit IncludeInFee(account);	
    }	
	

    
    function isExcludedFromFee(address account) external view returns(bool) {	
        return _isExcludedFromFee[account];
    }

    function totalFees() public view returns (uint256) {
        return _tFeeTotal;
    }
    
    function totalBurn() public view returns (uint256) {
        return _tBurnTotal;
    }

    
    function burn(uint256 amount) public returns(bool){

        burnFrom(msg.sender , amount);
        
        return(true);
    }

    function burnFrom(address account , uint256 amount) internal returns(bool){
        require(account != address(0), 'ERC20: burn from the zero address');

        _balances[account] = _balances[account].sub(amount, 'ERC20: burn amount exceeds balance');
        _totalSupply = _totalSupply.sub(amount);
        _tBurnTotal = _tBurnTotal.add(amount);
        emit Transfer(account, address(0), amount);
        
        return(true);
    }


    function _approve(address owner, address spender, uint256 amount) private {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }


        
   function _kinstransfer(address sender, address recipient, uint256 amount) internal {
       
        //if any account belongs to _isExcludedFromFee account then remove the fee	

        if (_isExcludedFromFee[sender] || _isExcludedFromFee[recipient] || !TakeFee) {
            _transfer(sender, recipient, amount);
        }
        else {
            
            require(amount <= _MAX_TX_SIZE , 'Amount larger than Max transfer limit');
            
            // A percentage of every transfer goes to Burn Vault ,ILP Vault & Dev
            uint256 farmAmount = amount.mul(_FARM_FEE).div(1000);
            uint256 burnAmount = amount.mul(_BURN_FEE).div(1000);
            uint256 ilpAmount = amount.mul(_ILP_FEE).div(1000);
            uint256 devAmount = amount.mul(_DEV_FEE).div(1000);
            uint256 marketingAmount = amount.mul(_MARKETING_FEE).div(1000);
            
            uint256 totalFee = farmAmount.add(burnAmount).add(ilpAmount).add(devAmount).add(marketingAmount); 
            
            
            // Remainder of transfer sent to recipient
            uint256 sendAmount = amount.sub(totalFee);
            require(amount == sendAmount + farmAmount + burnAmount + ilpAmount + devAmount + marketingAmount, "KINS Transfer: Fee value invalid");
            
            _tFeeTotal = _tFeeTotal.add(totalFee);

            burnFrom(sender, burnAmount);
            _transfer(sender, WFarm, farmAmount);
            _transfer(sender, WKinsIlp, ilpAmount);
            _transfer(sender, WDev, devAmount);
            _transfer(sender, WMarketing, marketingAmount);
            _transfer(sender, recipient, sendAmount);
            amount = sendAmount;
        }
    }
    
      /**
     * @dev Moves tokens `amount` from `sender` to `recipient`.
     *
     * This is internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal {
        require(sender != address(0), 'ERC20: transfer from the zero address');
        require(recipient != address(0), 'ERC20: transfer to the zero address');

        _balances[sender] = _balances[sender].sub(amount, 'ERC20: transfer amount exceeds balance');
        _balances[recipient] = _balances[recipient].add(amount);
        emit Transfer(sender, recipient, amount);
    }
    

    
}