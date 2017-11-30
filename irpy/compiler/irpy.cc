/*
 * Copyright 2017 Hyperkernel Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "PyLLVMEmitter.hh"
#include <ctime>

#if defined(PROFILER)
#include <gperftools/profiler.h>
#endif

inline static constexpr double cycles_to_ms(std::clock_t t) {
    return t / static_cast<double>(CLOCKS_PER_SEC / 1000.0);
}

int main(int argc, char **argv)
{

    llvm::LLVMContext ctx;
    llvm::SMDiagnostic err;
    const std::string filename = (argc < 2) ? "-" : std::string{argv[1]};

    std::clock_t start = std::clock();

    auto module = llvm::parseIRFile(filename, err, ctx);
    if (!module) {
        err.print("irpy", llvm::errs());
        return 3;
    }

    std::clock_t parsedone = std::clock();
    std::cerr << "Parsing took " << cycles_to_ms(parsedone - start) << " ms." << std::endl;

    irpy::PyLLVMEmitter emitter{std::cout, module.get()};

    #if defined(PROFILER)
    ProfilerStart("irpy.prof");
    #endif

    emitter.emitWarning(filename);
    emitter.emitModule();

    #if defined(PROFILER)
    ProfilerStop();
    #endif

    std::clock_t emitdone = std::clock();
    std::cerr << "Emitting took " << cycles_to_ms(emitdone - parsedone) << " ms." << std::endl;

    return 0;
}
