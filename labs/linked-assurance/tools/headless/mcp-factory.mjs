// SPDX-License-Identifier: Apache-2.0
import {createNodeDispatcher} from './dispatcher.mjs';
import {mcpFactory} from './mcp-adapter.mjs';
export async function createServerFactory(transport='mcp-stdio',config){
 const dispatcher=await createNodeDispatcher(transport,config);
 if(!dispatcher.profile.transports.includes(transport))throw Error('Transport disabled by site profile: '+transport);
 return mcpFactory(dispatcher,{name:'dickory-linked-assurance',version:'0.2.0'});
}
