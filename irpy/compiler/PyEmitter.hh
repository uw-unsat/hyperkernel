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

#pragma once

#include "Emitter.hh"

#include <tuple>
#include <iostream>
#include <vector>
#include <set>
#include <string>
#include <functional>

namespace irpy {

class PyEmitter : public Emitter
{

  public:
    PyEmitter(std::ostream &stream) : Emitter(stream)
    {
    }

    void genBlock(const std::string &blk, const std::function<void()> &body);

    void genDef(const std::string &name, const std::vector<std::string> &args,
                const std::function<void()> &func);

    void genException(const std::string &message) const;

    void emitWarning(const std::string &filename) const;

};

} // namespace irpy
