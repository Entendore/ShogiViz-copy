#!/bin/bash

# Exit immediately if a command exits with a non-zero status
set -e

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=================================================="
echo " YaneuraOu Auto-Installer for Linux & macOS"
echo "=================================================="

# 1. Detect Operating System and Set Compiler
OS="$(uname)"
if [ "$OS" = "Darwin" ]; then
    COMPILER="clang++"
    INSTALL_DIR="$HOME/YaneuraOu"
    echo "Detected OS: macOS (Using clang++)"
elif [ "$OS" = "Linux" ]; then
    COMPILER="g++"
    INSTALL_DIR="$HOME/YaneuraOu"
    echo "Detected OS: Linux (Using g++)"
else
    echo -e "${RED}This script is intended for Linux or macOS only.${NC}"
    exit 1
fi

# 2. Check for required tools
echo -e "\nChecking prerequisites..."
command -v make >/dev/null 2>&1 || { echo -e "${RED}Error: 'make' is not installed. Please install it first.${NC}"; exit 1; }
command -v curl >/dev/null 2>&1 || { echo -e "${RED}Error: 'curl' is not installed. Please install it first.${NC}"; exit 1; }
command -v unzip >/dev/null 2>&1 || { echo -e "${RED}Error: 'unzip' is not installed. Please install it first.${NC}"; exit 1; }
command -v $COMPILER >/dev/null 2>&1 || { echo -e "${RED}Error: '$COMPILER' is not installed. Please install your C++ compiler first.${NC}"; exit 1; }
echo -e "${GREEN}All prerequisites found!${NC}"

# 3. Download Source Code
mkdir -p "$INSTALL_DIR"
ZIP_FILE="$INSTALL_DIR/master.zip"

echo -e "\nDownloading YaneuraOu source code..."
curl -L -o "$ZIP_FILE" https://github.com/yaneurao/YaneuraOu/archive/refs/heads/master.zip

echo "Extracting files..."
unzip -o -q "$ZIP_FILE" -d "$INSTALL_DIR"

# Find the extracted directory (it usually names it YaneuraOu-master)
SOURCE_DIR=$(find "$INSTALL_DIR" -maxdepth 1 -type d -name "YaneuraOu-*" | head -n 1)/source

if [ ! -d "$SOURCE_DIR" ]; then
    echo -e "${RED}Error: Could not find the source directory after extraction.${NC}"
    exit 1
fi

echo -e "${GREEN}Source code ready at: $SOURCE_DIR${NC}"

# 4. Compile
echo -e "\nCompiling YaneuraOu (NNUE Edition for Puzzles/Evaluation)..."
echo "Using compiler: $COMPILER"

# -j$(nproc) uses all available CPU cores for faster compilation
cd "$SOURCE_DIR"
make -j"$(nproc 2>/dev/null || echo 4)" YANEURAOU_EDITION=YANEURAOU_ENGINE_NNUE COMPILER="$COMPILER"

# 5. Output Results
echo ""
echo "=================================================="
echo -e "${GREEN} ✅ COMPILATION SUCCESSFUL!${NC}"
echo "=================================================="
echo "Your YaneuraOu engine executable is located in:"
echo "$SOURCE_DIR"
echo ""

# 6. Important reminder for Evaluation/Puzzles
echo -e "${YELLOW}⚠️  IMPORTANT NEXT STEP FOR EVALUATION/PUZZLES ⚠️${NC}"
echo "YaneuraOu-NNUE requires an evaluation neural network file (e.g., nn.bin) to evaluate positions and solve puzzles."
echo ""
echo "1. Go to: https://github.com/yaneurao/YaneuraOu/releases"
echo "2. Download an eval file (usually named something like 'nn.bin' or 'suishou.nnue')."
echo "3. Move that file directly into the folder above."
echo "4. When loading the engine in your GUI/Script, send the command:"
echo "   setoption name EvalFile value [filename].bin"

# Clean up zip file
rm "$ZIP_FILE"