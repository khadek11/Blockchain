// Simplified Blockchain Implementation
// This code implements a basic blockchain with the following features:
// - Block and transaction data structures
// - Cryptographic hashing and signatures
// - Proof-of-work consensus algorithm
// - Transaction validation
// - Distributed ledger synchronization
// - Simple smart contract execution
// - Blockchain explorer and visualization
// - Network simulation for multiple nodes

#include <iostream>
#include <vector>
#include <string>
#include <sstream>
#include <ctime>
#include <algorithm>
#include <unordered_map>
#include <memory>
#include <random>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <queue>
#include <functional>
#include <iomanip>
#include <fstream>
#include <openssl/sha.h>
#include <openssl/rsa.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/bio.h>
#include <openssl/bn.h>
#include <cstdint>

const int DIFFICULTY = 3;      // Number of leading zeros required for proof-of-work
const int MINING_REWARD = 50;  // Reward for mining a block
const int BLOCK_SIZE = 10;     // Maximum number of transactions per block
const int TRANSACTION_FEE = 1; // Fee for processing a transaction

// Forward declarations
class SmartContract;
class MerkleTree;
class Transaction;
class Block;
class Blockchain;
class Wallet;
class Node;
class Network;
class BlockchainExplorer;

// ************ Utility Functions ************

// Function declarations for utility functions
std::string sha256(const std::string &str);
std::string generateRandomString(size_t length);
std::string getCurrentTimestamp();

// Convert string to SHA256 hash
std::string sha256(const std::string &str)
{
    unsigned char hash[SHA256_DIGEST_LENGTH];
    EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
    const EVP_MD *md = EVP_sha256();

    EVP_DigestInit_ex(mdctx, md, NULL);
    EVP_DigestUpdate(mdctx, str.c_str(), str.size());
    EVP_DigestFinal_ex(mdctx, hash, NULL);
    EVP_MD_CTX_free(mdctx);

    std::stringstream ss;
    for (int i = 0; i < SHA256_DIGEST_LENGTH; i++)
    {
        ss << std::hex << std::setw(2) << std::setfill('0') << (int)hash[i];
    }
    return ss.str();
}

// Generate random string for transaction IDs
std::string generateRandomString(size_t length)
{
    static const char alphanum[] =
        "0123456789"
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        "abcdefghijklmnopqrstuvwxyz";

    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> dis(0, sizeof(alphanum) - 2);

    std::string result;
    result.reserve(length);
    for (size_t i = 0; i < length; ++i)
    {
        result += alphanum[dis(gen)];
    }

    return result;
}

// Get current timestamp as string
std::string getCurrentTimestamp()
{
    std::time_t now = std::time(nullptr);
    std::tm *now_tm = std::localtime(&now);

    char buf[42];
    std::strftime(buf, 42, "%Y-%m-%d %H:%M:%S", now_tm);
    return std::string(buf);
}

// ************ Cryptography ************
class Cryptography
{
public:
    static void initialize()
    {
        // Initialize OpenSSL
        OpenSSL_add_all_algorithms();
        ERR_load_crypto_strings();
    }

    static void cleanup()
    {
        // Clean up OpenSSL
        EVP_cleanup();
        ERR_free_strings();
    }

    // Generate RSA key pair using modern API
    static std::pair<std::string, std::string> generateKeyPair()
    {
        EVP_PKEY *pkey = NULL;
        EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new_id(EVP_PKEY_RSA, NULL);

        EVP_PKEY_keygen_init(ctx);
        EVP_PKEY_CTX_set_rsa_keygen_bits(ctx, 2048);
        EVP_PKEY_keygen(ctx, &pkey);

        // Private key to PEM string
        BIO *privateBio = BIO_new(BIO_s_mem());
        PEM_write_bio_PrivateKey(privateBio, pkey, NULL, NULL, 0, NULL, NULL);
        char *privateKeyPtr;
        long privateKeyLength = BIO_get_mem_data(privateBio, &privateKeyPtr);
        std::string privateKey(privateKeyPtr, privateKeyLength);

        // Public key to PEM string
        BIO *publicBio = BIO_new(BIO_s_mem());
        PEM_write_bio_PUBKEY(publicBio, pkey);
        char *publicKeyPtr;
        long publicKeyLength = BIO_get_mem_data(publicBio, &publicKeyPtr);
        std::string publicKey(publicKeyPtr, publicKeyLength);

        // Clean up
        BIO_free(privateBio);
        BIO_free(publicBio);
        EVP_PKEY_free(pkey);
        EVP_PKEY_CTX_free(ctx);

        return {privateKey, publicKey};
    }

    // Sign a message using private key with modern API
    static std::string sign(const std::string &message, const std::string &privateKeyStr)
    {
        // Load private key
        BIO *bio = BIO_new_mem_buf(privateKeyStr.c_str(), -1);
        EVP_PKEY *pkey = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);

        // Create message digest
        unsigned char hash[SHA256_DIGEST_LENGTH];
        EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
        const EVP_MD *md = EVP_sha256();

        EVP_DigestInit_ex(mdctx, md, NULL);
        EVP_DigestUpdate(mdctx, message.c_str(), message.length());
        EVP_DigestFinal_ex(mdctx, hash, NULL);
        EVP_MD_CTX_free(mdctx);

        // Create signature
        EVP_MD_CTX *sign_ctx = EVP_MD_CTX_new();
        EVP_DigestSignInit(sign_ctx, NULL, md, NULL, pkey);

        size_t sig_len;
        EVP_DigestSignUpdate(sign_ctx, hash, SHA256_DIGEST_LENGTH);
        EVP_DigestSignFinal(sign_ctx, NULL, &sig_len);

        unsigned char *signature = (unsigned char *)OPENSSL_malloc(sig_len);
        EVP_DigestSignFinal(sign_ctx, signature, &sig_len);
        EVP_MD_CTX_free(sign_ctx);

        // Convert binary signature to hex string for storage/transmission
        std::stringstream ss;
        for (size_t i = 0; i < sig_len; i++)
        {
            ss << std::hex << std::setw(2) << std::setfill('0') << (int)signature[i];
        }

        // Clean up
        OPENSSL_free(signature);
        EVP_PKEY_free(pkey);
        BIO_free(bio);

        return ss.str();
    }

    // Verify a signature using public key with modern API
    static bool verify(const std::string &message, const std::string &signatureHex, const std::string &publicKeyStr)
    {
        // Load public key
        BIO *bio = BIO_new_mem_buf(publicKeyStr.c_str(), -1);
        EVP_PKEY *pkey = PEM_read_bio_PUBKEY(bio, NULL, NULL, NULL);

        // Convert hex signature back to binary
        std::vector<unsigned char> signature;
        for (size_t i = 0; i < signatureHex.length(); i += 2)
        {
            std::string byteString = signatureHex.substr(i, 2);
            unsigned char byte = (unsigned char)strtol(byteString.c_str(), nullptr, 16);
            signature.push_back(byte);
        }

        // Create hash of original message
        unsigned char hash[SHA256_DIGEST_LENGTH];
        EVP_MD_CTX *mdctx = EVP_MD_CTX_new();
        const EVP_MD *md = EVP_sha256();

        EVP_DigestInit_ex(mdctx, md, NULL);
        EVP_DigestUpdate(mdctx, message.c_str(), message.length());
        EVP_DigestFinal_ex(mdctx, hash, NULL);
        EVP_MD_CTX_free(mdctx);

        // Verify signature
        EVP_MD_CTX *verify_ctx = EVP_MD_CTX_new();
        EVP_DigestVerifyInit(verify_ctx, NULL, md, NULL, pkey);
        EVP_DigestVerifyUpdate(verify_ctx, hash, SHA256_DIGEST_LENGTH);
        int result = EVP_DigestVerifyFinal(verify_ctx, signature.data(), signature.size());
        EVP_MD_CTX_free(verify_ctx);

        // Clean up
        EVP_PKEY_free(pkey);
        BIO_free(bio);

        return (result == 1);
    }
};

class SmartContract
{
public:
    enum ContractType
    {
        TRANSFER,
        CONDITIONAL_TRANSFER,
        TOKEN_CREATION,
        CUSTOM
    };

private:
    std::string id;
    ContractType type;
    std::string code;
    std::unordered_map<std::string, std::string> state;

public:
    SmartContract(ContractType type, const std::string &code)
        : id(generateRandomString(16)), type(type), code(code) {}

    // Execute the smart contract
    bool execute(const std::unordered_map<std::string, std::string> &params)
    {
        // Simplified execution logic based on contract type
        switch (type)
        {
        case TRANSFER:
            return executeTransfer(params);
        case CONDITIONAL_TRANSFER:
            return executeConditionalTransfer(params);
        case TOKEN_CREATION:
            return executeTokenCreation(params);
        case CUSTOM:
            return executeCustom(params);
        default:
            return false;
        }
    }

    // Transfer tokens from one address to another
    bool executeTransfer(const std::unordered_map<std::string, std::string> &params)
    {
        // Check if required parameters are present
        if (params.find("from") == params.end() ||
            params.find("to") == params.end() ||
            params.find("amount") == params.end())
        {
            return false;
        }

        // In a real implementation, this would update balances
        // For this simplified version, we'll just update the state
        state["from"] = params.at("from");
        state["to"] = params.at("to");
        state["amount"] = params.at("amount");
        state["status"] = "completed";

        return true;
    }

    // Transfer tokens if a condition is met
    bool executeConditionalTransfer(const std::unordered_map<std::string, std::string> &params)
    {
        // Check if required parameters are present
        if (params.find("from") == params.end() ||
            params.find("to") == params.end() ||
            params.find("amount") == params.end() ||
            params.find("condition") == params.end())
        {
            return false;
        }

        // Check if the condition is met
        // For simplicity, we'll just check if the condition is "true"
        if (params.at("condition") != "true")
        {
            state["status"] = "condition_not_met";
            return false;
        }

        // Update state
        state["from"] = params.at("from");
        state["to"] = params.at("to");
        state["amount"] = params.at("amount");
        state["status"] = "completed";

        return true;
    }

    // Create a new token
    bool executeTokenCreation(const std::unordered_map<std::string, std::string> &params)
    {
        // Check if required parameters are present
        if (params.find("creator") == params.end() ||
            params.find("name") == params.end() ||
            params.find("symbol") == params.end() ||
            params.find("total_supply") == params.end())
        {
            return false;
        }

        // Update state
        state["creator"] = params.at("creator");
        state["name"] = params.at("name");
        state["symbol"] = params.at("symbol");
        state["total_supply"] = params.at("total_supply");
        state["status"] = "created";

        return true;
    }

    // Execute custom contract code
    bool executeCustom(const std::unordered_map<std::string, std::string> &params)
    {
        // In a real implementation, this would execute custom code
        // For this simplified version, we'll just check if the code contains
        // the required parameters and update the state

        for (const auto &pair : params)
        {
            // Check if the parameter is referenced in the code
            if (code.find(pair.first) != std::string::npos)
            {
                state[pair.first] = pair.second;
            }
        }

        state["status"] = "executed";
        return true;
    }

    std::string getId() const
    {
        return id;
    }

    ContractType getType() const
    {
        return type;
    }

    std::string getCode() const
    {
        return code;
    }

    std::unordered_map<std::string, std::string> getState() const
    {
        return state;
    }

    std::string getStateAsString() const
    {
        std::stringstream ss;
        for (const auto &pair : state)
        {
            ss << pair.first << ":" << pair.second << ";";
        }
        return ss.str();
    }
};

// Class for handling digital signatures

class MerkleTree
{
private:
    std::vector<std::string> leaves;
    std::vector<std::string> nodes;

public:
    MerkleTree(const std::vector<std::string> &data)
    {
        // Store the leaf hashes
        for (const auto &item : data)
        {
            leaves.push_back(sha256(item));
        }

        buildTree();
    }

    void buildTree()
    {
        nodes = leaves;

        // Build the tree bottom-up until we have a single root
        while (nodes.size() > 1)
        {
            std::vector<std::string> newLevel;

            // Process pairs of nodes
            for (size_t i = 0; i < nodes.size(); i += 2)
            {
                if (i + 1 < nodes.size())
                {
                    // Hash the pair of nodes
                    newLevel.push_back(sha256(nodes[i] + nodes[i + 1]));
                }
                else
                {
                    // If odd number of nodes, duplicate the last one
                    newLevel.push_back(sha256(nodes[i] + nodes[i]));
                }
            }

            nodes = newLevel;
        }
    }

    std::string getRoot() const
    {
        if (nodes.empty())
        {
            return "";
        }
        return nodes[0];
    }

    // Verify if a data item is in the tree
    bool verify(const std::string &data) const
    {
        std::string hash = sha256(data);

        // Check if the hash is in the leaves
        return std::find(leaves.begin(), leaves.end(), hash) != leaves.end();
    }

    // Get the proof for a specific data item
    std::vector<std::pair<bool, std::string>> getProof(const std::string &data) const
    {
        std::string hash = sha256(data);
        std::vector<std::pair<bool, std::string>> proof;

        // Find the index of the leaf
        auto it = std::find(leaves.begin(), leaves.end(), hash);
        if (it == leaves.end())
        {
            return proof; // Empty proof if data not found
        }

        size_t index = std::distance(leaves.begin(), it);
        std::vector<std::string> currentLevel = leaves;

        // Build the proof going up the tree
        while (currentLevel.size() > 1)
        {
            std::vector<std::string> nextLevel;

            // If index is even, we need the right sibling
            // If index is odd, we need the left sibling
            bool isRight = (index % 2 == 0);
            size_t siblingIndex = isRight ? index + 1 : index - 1;

            // Make sure the sibling exists
            if (siblingIndex < currentLevel.size())
            {
                proof.push_back({isRight, currentLevel[siblingIndex]});
            }
            else
            {
                // Use the same node if no sibling
                proof.push_back({isRight, currentLevel[index]});
            }

            // Move up the tree
            for (size_t i = 0; i < currentLevel.size(); i += 2)
            {
                if (i + 1 < currentLevel.size())
                {
                    nextLevel.push_back(sha256(currentLevel[i] + currentLevel[i + 1]));
                }
                else
                {
                    nextLevel.push_back(sha256(currentLevel[i] + currentLevel[i]));
                }
            }

            currentLevel = nextLevel;
            index = index / 2;
        }

        return proof;
    }

    // Verify a proof for a specific data item
    static bool verifyProof(const std::string &data, const std::vector<std::pair<bool, std::string>> &proof, const std::string &root)
    {
        std::string hash = sha256(data);

        // Apply the proof to compute the root
        for (const auto &step : proof)
        {
            if (step.first)
            {
                // Sibling is on the right
                hash = sha256(hash + step.second);
            }
            else
            {
                // Sibling is on the left
                hash = sha256(step.second + hash);
            }
        }

        // Check if the computed root matches the expected root
        return hash == root;
    }
};

class Transaction
{
private:
    std::string id;
    std::string sender;
    std::string recipient;
    double amount;
    double fee;
    std::string timestamp;
    std::string signature;
    std::shared_ptr<SmartContract> contract;
    bool isValid;

public:
    Transaction(const std::string &sender, const std::string &recipient, double amount)
        : id(generateRandomString(32)),
          sender(sender),
          recipient(recipient),
          amount(amount),
          fee(TRANSACTION_FEE),
          timestamp(getCurrentTimestamp()),
          isValid(false),
          contract(nullptr) {}

    // Constructor for reward transactions
    Transaction(const std::string &recipient, double amount)
        : id(generateRandomString(32)),
          sender("BLOCKCHAIN_REWARD"),
          recipient(recipient),
          amount(amount),
          fee(0),
          timestamp(getCurrentTimestamp()),
          isValid(true),
          contract(nullptr) {}

    // Constructor with smart contract
    Transaction(const std::string &sender, const std::string &recipient, double amount,
                std::shared_ptr<SmartContract> contract)
        : id(generateRandomString(32)),
          sender(sender),
          recipient(recipient),
          amount(amount),
          fee(TRANSACTION_FEE),
          timestamp(getCurrentTimestamp()),
          isValid(false),
          contract(contract) {}

    // Get data for signature/verification
    std::string getData() const
    {
        std::stringstream ss;
        ss << id << sender << recipient << amount << fee << timestamp;

        // Add contract data if present
        if (contract)
        {
            ss << contract->getId() << contract->getCode();
        }

        return ss.str();
    }

    // Sign the transaction
    void signTransaction(const std::string &privateKey)
    {
        std::string data = getData();
        signature = Cryptography::sign(data, privateKey);
        isValid = true;
    }

    // Verify the transaction signature
    bool verifySignature(const std::string &publicKey) const
    {
        if (sender == "BLOCKCHAIN_REWARD")
        {
            return true; // Reward transactions don't need verification
        }

        std::string data = getData();
        return Cryptography::verify(data, signature, publicKey);
    }

    // Execute smart contract if present
    bool executeContract(const std::unordered_map<std::string, std::string> &params)
    {
        if (!contract)
        {
            return false;
        }

        return contract->execute(params);
    }

    // Getters
    std::string getId() const { return id; }
    std::string getSender() const { return sender; }
    std::string getRecipient() const { return recipient; }
    double getAmount() const { return amount; }
    double getFee() const { return fee; }
    std::string getTimestamp() const { return timestamp; }
    std::string getSignature() const { return signature; }
    bool getIsValid() const { return isValid; }
    std::shared_ptr<SmartContract> getContract() const { return contract; }

    // Get transaction as string for hashing
    std::string toString() const
    {
        std::stringstream ss;
        ss << id << ";" << sender << ";" << recipient << ";"
           << amount << ";" << fee << ";" << timestamp << ";" << signature;

        // Add contract data if present
        if (contract)
        {
            ss << ";" << contract->getId() << ";" << contract->getStateAsString();
        }

        return ss.str();
    }
};

class Block
{
private:
    int index;
    std::string timestamp;
    std::vector<std::shared_ptr<Transaction>> transactions;
    std::string previousHash;
    std::string hash;
    int nonce;
    std::string merkleRoot;

public:
    Block(int index, const std::string &previousHash)
        : index(index),
          timestamp(getCurrentTimestamp()),
          previousHash(previousHash),
          nonce(0) {}

    // Add a transaction to the block
    bool addTransaction(std::shared_ptr<Transaction> transaction)
    {
        if (transactions.size() >= BLOCK_SIZE)
        {
            return false; // Block is full
        }

        transactions.push_back(transaction);
        return true;
    }

    // Calculate the Merkle root of transactions
    void calculateMerkleRoot()
    {
        std::vector<std::string> transactionStrings;
        for (const auto &tx : transactions)
        {
            transactionStrings.push_back(tx->toString());
        }

        // If no transactions, use a dummy value
        if (transactionStrings.empty())
        {
            transactionStrings.push_back("EMPTY_BLOCK");
        }

        MerkleTree merkleTree(transactionStrings);
        merkleRoot = merkleTree.getRoot();
    }

    // Calculate the hash of the block
    std::string calculateHash() const
    {
        std::stringstream ss;
        ss << index << timestamp << previousHash << merkleRoot << nonce;
        return sha256(ss.str());
    }

    // Mine the block (proof-of-work)
    void mineBlock(int difficulty)
    {
        calculateMerkleRoot();

        std::string target(difficulty, '0');

        while (true)
        {
            hash = calculateHash();
            if (hash.substr(0, difficulty) == target)
            {
                break;
            }
            nonce++;
        }

        std::cout << "Block mined: " << hash << std::endl;
    }

    // Verify the block
    bool isValid() const
    {
        // Verify hash
        if (hash != calculateHash())
        {
            return false;
        }

        // Verify proof-of-work
        std::string target(DIFFICULTY, '0');
        if (hash.substr(0, DIFFICULTY) != target)
        {
            return false;
        }

        // Verify transactions
        for (const auto &tx : transactions)
        {
            if (!tx->getIsValid())
            {
                return false;
            }
        }

        // Verify merkle root
        std::vector<std::string> transactionStrings;
        for (const auto &tx : transactions)
        {
            transactionStrings.push_back(tx->toString());
        }

        // If no transactions, use a dummy value
        if (transactionStrings.empty())
        {
            transactionStrings.push_back("EMPTY_BLOCK");
        }

        MerkleTree merkleTree(transactionStrings);
        if (merkleRoot != merkleTree.getRoot())
        {
            return false;
        }

        return true;
    }

    // Getters
    int getIndex() const { return index; }
    std::string getTimestamp() const { return timestamp; }
    std::vector<std::shared_ptr<Transaction>> getTransactions() const { return transactions; }
    std::string getPreviousHash() const { return previousHash; }
    std::string getHash() const { return hash; }
    int getNonce() const { return nonce; }
    std::string getMerkleRoot() const { return merkleRoot; }

    // Setters
    void setHash(const std::string &h) { hash = h; }

    // Get block as string for display
    std::string toString() const
    {
        std::stringstream ss;
        ss << "Block #" << index << "\n";
        ss << "Timestamp: " << timestamp << "\n";
        ss << "Previous Hash: " << previousHash << "\n";
        ss << "Merkle Root: " << merkleRoot << "\n";
        ss << "Hash: " << hash << "\n";
        ss << "Nonce: " << nonce << "\n";
        ss << "Transactions: " << transactions.size() << "\n";

        for (size_t i = 0; i < transactions.size(); i++)
        {
            const auto &tx = transactions[i];
            ss << "  " << i + 1 << ". " << tx->getSender() << " -> "
               << tx->getRecipient() << ": " << tx->getAmount() << "\n";
        }

        return ss.str();
    }
};

// ************ Blockchain ************

// Blockchain class - MOVED UP before classes that depend on it
class Blockchain
{
private:
    std::vector<std::shared_ptr<Block>> chain;
    std::vector<std::shared_ptr<Transaction>> pendingTransactions;
    std::unordered_map<std::string, std::string> walletAddresses; // Public key to address mapping
    std::unordered_map<std::string, double> balances;
    std::unordered_map<std::string, std::shared_ptr<SmartContract>> contracts;
    std::mutex chainMutex;
    std::mutex pendingTransactionsMutex;

public:
    Blockchain()
    {
        // Create genesis block
        createGenesisBlock();
    }

    // Create the first block in the chain
    void createGenesisBlock()
    {
        std::shared_ptr<Block> genesisBlock = std::make_shared<Block>(0, "0");
        genesisBlock->calculateMerkleRoot();
        genesisBlock->setHash(sha256("genesis"));

        chain.push_back(genesisBlock);
    }

    // Get the latest block in the chain
    std::shared_ptr<Block> getLatestBlock() const
    {
        return chain.back();
    }

    // Add a new block to the chain
    bool addBlock(std::shared_ptr<Block> newBlock)
    {
        std::lock_guard<std::mutex> lock(chainMutex);

        // Ensure the new block points to the latest block
        if (newBlock->getPreviousHash() != getLatestBlock()->getHash())
        {
            return false;
        }

        // Mine the block
        newBlock->mineBlock(DIFFICULTY);

        // Verify the block
        if (!newBlock->isValid())
        {
            return false;
        }

        // Add the block to the chain
        chain.push_back(newBlock);

        // Update balances based on the transactions
        updateBalances(newBlock);

        return true;
    }

    // Add a transaction to pending transactions
    bool addTransaction(std::shared_ptr<Transaction> transaction)
    {
        std::lock_guard<std::mutex> lock(pendingTransactionsMutex);

        // Verify the transaction
        if (!transaction->getIsValid())
        {
            return false;
        }

        // Check if sender has enough balance
        if (transaction->getSender() != "BLOCKCHAIN_REWARD")
        {
            double senderBalance = getBalance(transaction->getSender());
            if (senderBalance < (transaction->getAmount() + transaction->getFee()))
            {
                return false;
            }
        }

        // Add the transaction to pending transactions
        pendingTransactions.push_back(transaction);

        return true;
    }

    // Process pending transactions into a new block
    bool minePendingTransactions(const std::string &minerAddress)
    {
        std::lock_guard<std::mutex> lock1(pendingTransactionsMutex);

        // Check if there are any pending transactions
        if (pendingTransactions.empty())
        {
            return false;
        }

        // Create a new block
        int newIndex = getLatestBlock()->getIndex() + 1;
        std::shared_ptr<Block> newBlock = std::make_shared<Block>(newIndex, getLatestBlock()->getHash());

        // Add pending transactions to the block (up to BLOCK_SIZE)
        int count = 0;
        while (!pendingTransactions.empty() && count < BLOCK_SIZE)
        {
            newBlock->addTransaction(pendingTransactions.front());
            pendingTransactions.erase(pendingTransactions.begin());
            count++;
        }

        // Add mining reward transaction
        std::shared_ptr<Transaction> rewardTransaction =
            std::make_shared<Transaction>(minerAddress, MINING_REWARD);
        newBlock->addTransaction(rewardTransaction);

        // Add the block to the chain
        std::lock_guard<std::mutex> lock2(chainMutex);
        return addBlock(newBlock);
    }

    // Update balances based on the transactions in a block
    void updateBalances(std::shared_ptr<Block> block)
    {
        for (const auto &tx : block->getTransactions())
        {
            // Deduct amount from sender
            if (tx->getSender() != "BLOCKCHAIN_REWARD")
            {
                double senderBalance = getBalance(tx->getSender());
                balances[tx->getSender()] = senderBalance - tx->getAmount() - tx->getFee();
            }

            // Add amount to recipient
            double recipientBalance = getBalance(tx->getRecipient());
            balances[tx->getRecipient()] = recipientBalance + tx->getAmount();

            // Execute smart contract if present
            if (tx->getContract())
            {
                std::unordered_map<std::string, std::string> params = {
                    {"from", tx->getSender()},
                    {"to", tx->getRecipient()},
                    {"amount", std::to_string(tx->getAmount())}};

                tx->executeContract(params);

                // Store the contract in the blockchain
                contracts[tx->getContract()->getId()] = tx->getContract();
            }
        }
    }

    // Check if the blockchain is valid
    bool isValid() const
    {
        for (size_t i = 1; i < chain.size(); i++)
        {
            const auto &currentBlock = chain[i];
            const auto &previousBlock = chain[i - 1];

            // Check if the current block is valid
            if (!currentBlock->isValid())
            {
                return false;
            }

            // Check if the current block points to the previous block
            if (currentBlock->getPreviousHash() != previousBlock->getHash())
            {
                return false;
            }
        }

        return true;
    }

    // Register a wallet address
    void registerWalletAddress(const std::string &publicKey, const std::string &address)
    {
        walletAddresses[publicKey] = address;
        balances[address] = 0; // Initialize balance to zero
    }

    // Get the address for a public key
    std::string getAddressForPublicKey(const std::string &publicKey) const
    {
        auto it = walletAddresses.find(publicKey);
        if (it != walletAddresses.end())
        {
            return it->second;
        }
        return "";
    }

    // Get the balance for an address
    double getBalance(const std::string &address) const
    {
        auto it = balances.find(address);
        if (it != balances.end())
        {
            return it->second;
        }
        return 0.0;
    }

    // Deploy a smart contract
    std::string deploySmartContract(std::shared_ptr<SmartContract> contract)
    {
        std::string contractId = contract->getId();
        contracts[contractId] = contract;
        return contractId;
    }

    // Get a smart contract by ID
    std::shared_ptr<SmartContract> getSmartContract(const std::string &contractId) const
    {
        auto it = contracts.find(contractId);
        if (it != contracts.end())
        {
            return it->second;
        }
        return nullptr;
    }

    // Get the chain
    std::vector<std::shared_ptr<Block>> getChain() const
    {
        return chain;
    }

    // Get pending transactions
    std::vector<std::shared_ptr<Transaction>> getPendingTransactions() const
    {
        return pendingTransactions;
    }

    // Replace the chain with a longer valid chain
    bool replaceChain(const std::vector<std::shared_ptr<Block>> &newChain)
    {
        std::lock_guard<std::mutex> lock(chainMutex);

        // Check if the new chain is longer
        if (newChain.size() <= chain.size())
        {
            return false;
        }

        // Check if the new chain is valid
        for (size_t i = 1; i < newChain.size(); i++)
        {
            const auto &currentBlock = newChain[i];
            const auto &previousBlock = newChain[i - 1];

            // Check if the current block is valid
            if (!currentBlock->isValid())
            {
                return false;
            }

            // Check if the current block points to the previous block
            if (currentBlock->getPreviousHash() != previousBlock->getHash())
            {
                return false;
            }
        }

        // Replace the chain
        chain = newChain;

        // Reset balances and recalculate
        balances.clear();
        for (const auto &block : chain)
        {
            updateBalances(block);
        }

        return true;
    }

    // Get the blockchain as string for display
    std::string toString() const
    {
        std::stringstream ss;
        ss << "Blockchain:\n";

        for (const auto &block : chain)
        {
            ss << "--------------------\n";
            ss << block->toString();
        }

        ss << "--------------------\n";
        ss << "Pending Transactions: " << pendingTransactions.size() << "\n";

        return ss.str();
    }
};

// ************ Wallet ************

// Wallet class for managing keys and transactions
class Wallet
{
private:
    std::string privateKey;
    std::string publicKey;
    std::string address;

public:
    Wallet()
    {
        generateKeyPair();
        generateAddress();
    }

    // Generate a new key pair
    void generateKeyPair()
    {
        auto keyPair = Cryptography::generateKeyPair();
        privateKey = keyPair.first;
        publicKey = keyPair.second;
    }

    // Generate a wallet address from the public key
    void generateAddress()
    {
        // Simple address generation: hash of public key
        address = sha256(publicKey).substr(0, 40);
    }

    // Create a transaction
    std::shared_ptr<Transaction> createTransaction(const std::string &recipient, double amount)
    {
        auto transaction = std::make_shared<Transaction>(address, recipient, amount);
        transaction->signTransaction(privateKey);
        return transaction;
    }

    // Create a transaction with a smart contract
    std::shared_ptr<Transaction> createTransaction(const std::string &recipient, double amount,
                                                   std::shared_ptr<SmartContract> contract)
    {
        auto transaction = std::make_shared<Transaction>(address, recipient, amount, contract);
        transaction->signTransaction(privateKey);
        return transaction;
    }

    // Getters
    std::string getPrivateKey() const { return privateKey; }
    std::string getPublicKey() const { return publicKey; }
    std::string getAddress() const { return address; }
};

// ************ Node ************

// Node class for participating in the network
class Node
{
private:
    std::string id;
    std::shared_ptr<Blockchain> blockchain;
    std::shared_ptr<Wallet> wallet;
    std::vector<std::string> peers;
    bool isMining;
    std::thread miningThread;
    std::mutex peersMutex;
    std::condition_variable miningCV;
    bool stopMiningFlag; // Renamed from stopMining to avoid conflicts

public:
    Node()
        : id(generateRandomString(16)),
          blockchain(std::make_shared<Blockchain>()),
          wallet(std::make_shared<Wallet>()),
          isMining(false),
          stopMiningFlag(false)
    {
        // Register the wallet with the blockchain
        blockchain->registerWalletAddress(wallet->getPublicKey(), wallet->getAddress());
    }

    ~Node()
    {
        stopMiningFlag = true;
        miningCV.notify_all();
        if (miningThread.joinable())
        {
            miningThread.join();
        }
    }

    // Add a peer to the node
    void addPeer(const std::string &peerAddress)
    {
        std::lock_guard<std::mutex> lock(peersMutex);
        if (std::find(peers.begin(), peers.end(), peerAddress) == peers.end())
        {
            peers.push_back(peerAddress);
        }
    }

    // Remove a peer from the node
    void removePeer(const std::string &peerAddress)
    {
        std::lock_guard<std::mutex> lock(peersMutex);
        auto it = std::find(peers.begin(), peers.end(), peerAddress);
        if (it != peers.end())
        {
            peers.erase(it);
        }
    }

    // Broadcast a transaction to all peers
    void broadcastTransaction(std::shared_ptr<Transaction> transaction)
    {
        // In a real implementation, this would send the transaction to all peers
        // For this simplified version, we'll just add it to our own blockchain
        blockchain->addTransaction(transaction);
    }

    // Broadcast a new block to all peers
    void broadcastBlock(std::shared_ptr<Block> block)
    {
        // In a real implementation, this would send the block to all peers
        // For this simplified version, we'll just add it to our own blockchain
        blockchain->addBlock(block);
    }

    // Start mining blocks
    void startMining()
    {
        if (isMining)
        {
            return;
        }

        isMining = true;
        stopMiningFlag = false;

        miningThread = std::thread([this]()
                                   {
            while (!stopMiningFlag) {
                // Mine a block
                if (blockchain->minePendingTransactions(wallet->getAddress())) {
                    std::cout << "Node " << id << " mined a block!" << std::endl;
                }
                
                // Sleep to simulate network delay
                std::this_thread::sleep_for(std::chrono::seconds(15));
                
                // Wait for signal to stop mining
                std::unique_lock<std::mutex> lock(peersMutex);
                miningCV.wait_for(lock, std::chrono::seconds(1), [this]() { return stopMiningFlag; });
            } });
    }

    // Stop mining blocks
    void stopMining()
    {
        if (!isMining)
        {
            return;
        }

        isMining = false;
        stopMiningFlag = true;
        miningCV.notify_all();

        if (miningThread.joinable())
        {
            miningThread.join();
        }
    }

    // Create a transaction
    std::shared_ptr<Transaction> createTransaction(const std::string &recipient, double amount)
    {
        return wallet->createTransaction(recipient, amount);
    }

    // Deploy a smart contract
    std::string deploySmartContract(SmartContract::ContractType type, const std::string &code)
    {
        auto contract = std::make_shared<SmartContract>(type, code);
        return blockchain->deploySmartContract(contract);
    }

    // Synchronize with the network
    void synchronize(std::shared_ptr<Node> peer)
    {
        // Get the peer's blockchain
        auto peerChain = peer->getBlockchain()->getChain();

        // Check if the peer's chain is longer
        if (peerChain.size() > blockchain->getChain().size())
        {
            // Replace our chain with the peer's chain
            blockchain->replaceChain(peerChain);
        }
    }

    // Getters
    std::string getId() const { return id; }
    std::shared_ptr<Blockchain> getBlockchain() const { return blockchain; }
    std::shared_ptr<Wallet> getWallet() const { return wallet; }
    std::vector<std::string> getPeers()
    {
        std::lock_guard<std::mutex> lock(peersMutex);
        return peers;
    }
    bool getIsMining() const { return isMining; }
};

// ************ Network ************

// Network class for simulating a blockchain network
class Network
{
private:
    std::vector<std::shared_ptr<Node>> nodes;
    mutable std::mutex nodesMutex; // Changed to mutable to allow locking in const methods

public:
    // Add a node to the network
    void addNode(std::shared_ptr<Node> node)
    {
        std::lock_guard<std::mutex> lock(nodesMutex);
        nodes.push_back(node);

        // Add the node as a peer to all other nodes
        for (const auto &otherNode : nodes)
        {
            if (otherNode->getId() != node->getId())
            {
                otherNode->addPeer(node->getId());
                node->addPeer(otherNode->getId());
            }
        }
    }

    // Remove a node from the network
    void removeNode(const std::string &nodeId)
    {
        std::lock_guard<std::mutex> lock(nodesMutex);

        // Find the node
        auto it = std::find_if(nodes.begin(), nodes.end(),
                               [nodeId](const std::shared_ptr<Node> &node)
                               {
                                   return node->getId() == nodeId;
                               });

        if (it != nodes.end())
        {
            // Remove the node as a peer from all other nodes
            for (const auto &otherNode : nodes)
            {
                if (otherNode->getId() != nodeId)
                {
                    otherNode->removePeer(nodeId);
                }
            }

            // Remove the node from the network
            nodes.erase(it);
        }
    }

    // Start mining on all nodes
    void startMining()
    {
        std::lock_guard<std::mutex> lock(nodesMutex);
        for (const auto &node : nodes)
        {
            node->startMining();
        }
    }

    // Stop mining on all nodes
    void stopMining()
    {
        std::lock_guard<std::mutex> lock(nodesMutex);
        for (const auto &node : nodes)
        {
            node->stopMining();
        }
    }

    // Simulate a transaction between two nodes
    void simulateTransaction(const std::string &fromNodeId, const std::string &toNodeId, double amount)
    {
        std::lock_guard<std::mutex> lock(nodesMutex);

        // Find the nodes
        auto fromNode = std::find_if(nodes.begin(), nodes.end(),
                                     [fromNodeId](const std::shared_ptr<Node> &node)
                                     {
                                         return node->getId() == fromNodeId;
                                     });

        auto toNode = std::find_if(nodes.begin(), nodes.end(),
                                   [toNodeId](const std::shared_ptr<Node> &node)
                                   {
                                       return node->getId() == toNodeId;
                                   });

        if (fromNode != nodes.end() && toNode != nodes.end())
        {
            // Create and broadcast the transaction
            auto transaction = (*fromNode)->createTransaction((*toNode)->getWallet()->getAddress(), amount);
            (*fromNode)->broadcastTransaction(transaction);
        }
    }

    // Synchronize all nodes
    void synchronizeNodes()
    {
        std::lock_guard<std::mutex> lock(nodesMutex);

        for (size_t i = 0; i < nodes.size(); i++)
        {
            for (size_t j = i + 1; j < nodes.size(); j++)
            {
                nodes[i]->synchronize(nodes[j]);
                nodes[j]->synchronize(nodes[i]);
            }
        }
    }

    // Get the nodes
    std::vector<std::shared_ptr<Node>> getNodes() const
    {
        std::lock_guard<std::mutex> lock(nodesMutex);
        return nodes;
    }
};

// ************ BlockchainExplorer ************

// BlockchainExplorer class for visualizing the blockchain
class BlockchainExplorer
{
private:
    std::shared_ptr<Blockchain> blockchain;

public:
    BlockchainExplorer(std::shared_ptr<Blockchain> blockchain)
        : blockchain(blockchain) {}

    // Print the entire blockchain
    void printBlockchain() const
    {
        std::cout << blockchain->toString() << std::endl;
    }

    // Save the blockchain to a file
    void saveBlockchainToFile(const std::string &filename) const
    {
        std::ofstream file(filename);
        file << blockchain->toString();
        file.close();
    }

    // Print a specific block
    void printBlock(int index) const
    {
        if (index < 0 || index >= static_cast<int>(blockchain->getChain().size()))
        {
            std::cout << "Block index out of range." << std::endl;
            return;
        }

        std::cout << blockchain->getChain()[index]->toString() << std::endl;
    }

    // Print all transactions for an address
    void printAddressTransactions(const std::string &address) const
    {
        std::cout << "Transactions for address " << address << ":" << std::endl;

        int count = 0;
        for (const auto &block : blockchain->getChain())
        {
            for (const auto &tx : block->getTransactions())
            {
                if (tx->getSender() == address || tx->getRecipient() == address)
                {
                    std::cout << "Block #" << block->getIndex() << " | ";
                    std::cout << tx->getSender() << " -> " << tx->getRecipient() << ": " << tx->getAmount() << std::endl;
                    count++;
                }
            }
        }

        std::cout << "Total transactions: " << count << std::endl;
    }

    // Print all smart contracts
    void printSmartContracts() const
    {
        std::cout << "Smart Contracts:" << std::endl;

        int count = 0;
        for (const auto &block : blockchain->getChain())
        {
            for (const auto &tx : block->getTransactions())
            {
                auto contract = tx->getContract();
                if (contract)
                {
                    std::cout << "Block #" << block->getIndex() << " | ";
                    std::cout << "Contract ID: " << contract->getId() << " | ";
                    std::cout << "Type: " << contract->getType() << std::endl;
                    count++;
                }
            }
        }

        std::cout << "Total contracts: " << count << std::endl;
    }

    // Generate a graphical representation of the blockchain
    void generateBlockchainGraph(const std::string &filename) const
    {
        std::ofstream file(filename);

        // Generate a simple ASCII art representation
        file << "Blockchain Graph:" << std::endl;
        file << "-----------------" << std::endl;

        for (size_t i = 0; i < blockchain->getChain().size(); i++)
        {
            const auto &block = blockchain->getChain()[i];
            file << "Block #" << block->getIndex() << " [" << block->getHash().substr(0, 8) << "...]";

            // Add arrow to next block
            if (i < blockchain->getChain().size() - 1)
            {
                file << " ---> ";
            }

            // Add new line every 3 blocks for readability
            if ((i + 1) % 3 == 0)
            {
                file << std::endl;
            }
        }

        file.close();
    }
};

// ************ Main Function ************

int main()
{
    // Initialize cryptography
    Cryptography::initialize();

    // Create blockchain network
    Network network;

    // Create nodes
    auto node1 = std::make_shared<Node>();
    auto node2 = std::make_shared<Node>();
    auto node3 = std::make_shared<Node>();

    // Add nodes to the network
    network.addNode(node1);
    network.addNode(node2);
    network.addNode(node3);

    std::cout << "Blockchain network created with 3 nodes." << std::endl;
    std::cout << "Node 1 address: " << node1->getWallet()->getAddress() << std::endl;
    std::cout << "Node 2 address: " << node2->getWallet()->getAddress() << std::endl;
    std::cout << "Node 3 address: " << node3->getWallet()->getAddress() << std::endl;

    // Create some transactions
    auto tx1 = node1->createTransaction(node2->getWallet()->getAddress(), 10.0);
    node1->broadcastTransaction(tx1);

    auto tx2 = node2->createTransaction(node3->getWallet()->getAddress(), 5.0);
    node2->broadcastTransaction(tx2);

    // Deploy a smart contract
    std::string contractCode = "function transfer(from, to, amount) { return true; }";
    std::string contractId = node1->deploySmartContract(SmartContract::TRANSFER, contractCode);
    std::cout << "Deployed smart contract with ID: " << contractId << std::endl;

    // Start mining
    std::cout << "Starting mining..." << std::endl;
    network.startMining();

    // Wait for some blocks to be mined
    std::this_thread::sleep_for(std::chrono::seconds(5));

    // Stop mining
    network.stopMining();
    std::cout << "Mining stopped." << std::endl;

    // Synchronize nodes
    network.synchronizeNodes();
    std::cout << "Nodes synchronized." << std::endl;

    // Create blockchain explorer
    BlockchainExplorer explorer(node1->getBlockchain());

    // Print the blockchain
    std::cout << "\nBlockchain Explorer:" << std::endl;
    explorer.printBlockchain();

    // Generate blockchain graph
    explorer.generateBlockchainGraph("blockchain_graph.txt");
    std::cout << "Blockchain graph saved to blockchain_graph.txt" << std::endl;

    // Cleanup
    Cryptography::cleanup();

    return 0;
}
