//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/TestPass.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
// L'include seguente va in LocalOpts.h
#include <llvm/IR/Constants.h>
//Include inserita per funzioni ReplaceInstWithValue, ReplaceInstWithInst
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

using namespace llvm;
void print_algebrical_identity(Instruction& i, Value *op, bool AddOrMul){
  if(AddOrMul == true){
    outs() << "ADD ALGEBRICAL IDENTITY\n";
  } else{
    outs() << "MUL ALGEBRICAL IDENTITY\n";
  }
  outs() << "\tUSES OF " ;
  i.printAsOperand(outs(), false);
  outs() << " REPLACE WITH: ";
  op->printAsOperand(outs(), false);
  outs() << "\n";
}



void AlgebricIdentity(BasicBlock &B){
  Value *op1, *op2;
  for(Instruction &inst : B){
    //Add algebrical identity
    if(inst.getOpcode() == Instruction::Add){
      op1 = inst.getOperand(0);
      op2 = inst.getOperand(1);
      if(ConstantInt *C = dyn_cast<ConstantInt>(op1)){
        if(C->getValue()==0){
          print_algebrical_identity(inst, op2, true);
          inst.replaceAllUsesWith(op2);
        }
      }
      if(ConstantInt *C = dyn_cast<ConstantInt>(op2)){
        if(C->getValue()==0){
          print_algebrical_identity(inst, op1, true);
          inst.replaceAllUsesWith(op1);
        }
      }
    }
    //Mul algebrical identity
    if(inst.getOpcode() == Instruction::Mul){
      op1 = inst.getOperand(0);
      op2 = inst.getOperand(1);
      if(ConstantInt *C = dyn_cast<ConstantInt>(op1)){
        if(C->getValue()==1){
          print_algebrical_identity(inst, op2, false);
          inst.replaceAllUsesWith(op2);
        }
      }
      if(ConstantInt *C = dyn_cast<ConstantInt>(op2)){
        if(C->getValue()==1){
          print_algebrical_identity(inst, op1, false);
          inst.replaceAllUsesWith(op1);
        }
      }
    }

  }
}

bool runOnBasicBlock(BasicBlock &B) {  
  //Print all instruction
  /* outs() << "--------------------------------\n\n";

  for(Instruction &inst : B){
    outs() << inst << "\t OPCODE" << inst.getOpcode() << "\n";
    for (auto *Iter = inst.op_begin(); Iter != inst.op_end(); ++Iter) {
      Value *Operand = *Iter;
       if (Argument *Arg = dyn_cast<Argument>(Operand)) {
        outs() << "\t" << *Arg << ": SONO L'ARGOMENTO N. " << Arg->getArgNo() 
          <<" DELLA FUNZIONE " << Arg->getParent()->getName()
                << "\n";
      } 
      else{
        if (ConstantInt *C = dyn_cast<ConstantInt>(Operand)) {
           outs() << "\t" << *C << ": SONO UNA COSTANTE INTERA DI VALORE " << C->getValue()
                   << "\n"; 
          //algebric identity
          if((C->getValue() == 0 && inst.getOpcode() == Instruction::Add) || (C->getValue() == 1 && inst.getOpcode() == Instruction::Mul)){
            
          }
        }
         else{
          outs() << "\t  OPERANDO" << *Operand << "\n";
        } 
      }
    }
  }
  outs() << "\n--------------------------------\n\n\n"; */

  AlgebricIdentity(B);

  // Preleviamo le prime due istruzioni del BB
  Instruction &Inst1st = *B.begin(), &Inst2nd = *(++B.begin());

  // L'indirizzo della prima istruzione deve essere uguale a quello del 
  // primo operando della seconda istruzione (per costruzione dell'esempio)
  assert(&Inst1st == Inst2nd.getOperand(0));

  // Stampa la prima istruzione
  outs() << "PRIMA ISTRUZIONE: " << Inst1st << "\n";
  // Stampa la prima istruzione come operando
  outs() << "COME OPERANDO: ";
  Inst1st.printAsOperand(outs(), false);
  outs() << "\n";

  // User-->Use-->Value
  outs() << "I MIEI OPERANDI SONO:\n";
  for (auto *Iter = Inst1st.op_begin(); Iter != Inst1st.op_end(); ++Iter) {
    Value *Operand = *Iter;

    if (Argument *Arg = dyn_cast<Argument>(Operand)) {
      outs() << "\t" << *Arg << ": SONO L'ARGOMENTO N. " << Arg->getArgNo() 
        <<" DELLA FUNZIONE " << Arg->getParent()->getName()
              << "\n";
    }
    if (ConstantInt *C = dyn_cast<ConstantInt>(Operand)) {
      outs() << "\t" << *C << ": SONO UNA COSTANTE INTERA DI VALORE " << C->getValue()
              << "\n";
    }
  }

  outs() << "LA LISTA DEI MIEI USERS:\n";
  for (auto Iter = Inst1st.user_begin(); Iter != Inst1st.user_end(); ++Iter) {
    outs() << "\t" << *(dyn_cast<Instruction>(*Iter)) << "\n";
  }

  outs() << "E DEI MIEI USI (CHE E' LA STESSA):\n";
  for (auto Iter = Inst1st.use_begin(); Iter != Inst1st.use_end(); ++Iter) {
    outs() << "\t" << *(dyn_cast<Instruction>(Iter->getUser())) << "\n";
  }

  // Manipolazione delle istruzioni
  Instruction *NewInst = BinaryOperator::Create(
      Instruction::Add, Inst1st.getOperand(0), Inst1st.getOperand(0));

  NewInst->insertAfter(&Inst1st);
  // Si possono aggiornare le singole references separatamente?
  // Controlla la documentazione e prova a rispondere.
  Inst1st.replaceAllUsesWith(NewInst);

  return true;
}


bool runOnFunction(Function &F) {
  bool Transformed = false;
  for (auto Iter = F.begin(); Iter != F.end(); ++Iter) {
    if (runOnBasicBlock(*Iter)) {
      Transformed = true;
    }
  }

  return Transformed;
}


PreservedAnalyses TestPass::run(Module &M, ModuleAnalysisManager &AM) {
  for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
    if (runOnFunction(*Fiter))
      return PreservedAnalyses::none();
  
  return PreservedAnalyses::all();
}

