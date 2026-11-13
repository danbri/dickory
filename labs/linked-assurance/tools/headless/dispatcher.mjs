// SPDX-License-Identifier: Apache-2.0
import fs from 'node:fs/promises';
import {createDispatcher} from '../../profile/core.js';
import {workbenchProfile} from '../../profile/catalogue.js';
import {listCases} from '../../headless-contract.js';
import {runNodeCase} from './node-runner.mjs';
import {runNativePolicyCase,checkNativePolicy} from './policy-runner.mjs';
export async function createNodeDispatcher(transport='local-cli',config){
 if(!config){const file=process.env.LINKED_PROFILE||new URL('../../developer-profile.json',import.meta.url);config=JSON.parse(await fs.readFile(file,'utf8'));}
 return createDispatcher({profile:workbenchProfile(config),transport,capabilities:['rdf','lean-policy'],
  runtime:{host:'node',node:process.versions.node,executable:process.execPath},handlers:{
   linked_assurance_cases:()=>({cases:listCases()}),linked_assurance_evaluate:runNodeCase,
   linked_assurance_check_policy:(_input,options)=>checkNativePolicy(options),linked_assurance_policy:runNativePolicyCase
  }});
}
