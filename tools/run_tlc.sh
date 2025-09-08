#!/bin/bash

set -e

MODEL_NAME=$1
if [ -z "$MODEL_NAME" ]; then
    echo "Usage: $0 <model_name>"
    exit 1
fi

MODEL_FILE="models/${MODEL_NAME}.cfg"
SPEC_FILE="specs/tla/VotorCore.tla"

if [ ! -f "$MODEL_FILE" ]; then
    echo "Model file not found: $MODEL_FILE"
    exit 1
fi

if [ ! -f "$SPEC_FILE" ]; then
    echo "Spec file not found: $SPEC_FILE"
    exit 1
fi

echo "Running TLC model checker on $MODEL_NAME..."
echo "Spec: $SPEC_FILE"
echo "Model: $MODEL_FILE"
echo ""

java -cp tla2tools.jar tlc2.TLC \
    -config "$MODEL_FILE" \
    -modelcheck \
    -deadlock \
    -workers auto \
    "$SPEC_FILE"

echo ""
echo "TLC model checking complete for $MODEL_NAME"