# Makefile for Blockchain Implementation

CXX = g++
CXXFLAGS = -std=c++11 -pthread
LDFLAGS = -lssl -lcrypto

TARGET = blockchain
SOURCES = blockchain.cpp

all: $(TARGET)

$(TARGET): $(SOURCES)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(SOURCES) $(LDFLAGS)

clean:
	rm -f $(TARGET)

run: $(TARGET)
	./$(TARGET)