import { ipcMain } from 'electron';
import { Server } from 'http';
import { connect } from 'http2';

const { exec } = require("child_process");

// "ipc" in "ipcMain" stands for "Inter-Process Communication": this is the
// object that enables communication between the Renderer process (the browser
// window) and the Main process, which is allowed to perform system calls.

// Here we use ipcMain to bind event listeners to the Main process: they will be
// triggered from the Renderer process (e.g. in index.vue) so that we can send
// TCP requests to the Python speech daemon when entering speech recognition
// mode in the interface.


// We will use the net module to establish a tcp connection between electron and 
// the python server which listen to the user's microphone
const net = require('net');
const Port = 42000;
var Server_socket;
// 'State' is the variable we use to determine whether we listen to the user or not
// State==0: Speech recognition is off
// State==1: Speech recognition is on
var State = -1;

let spawn = require("child_process").spawn;


export default {
    startDaemon: function (win) {
      // TODO
    },
    bindEvents: function (win) {
        // Bind a listener to a new event named "vocalCommand", which just sends
        // back the sentence spoken by the user to the Renderer. The logic of
        // listening in a loop until a valid command is uttered is implemented
        // in the Renderer, so that we can request the list of available actions
        // from Actema's proof engine.


        // Bind a listener to a new event named "stopListening", which instructs
        // the speech daemon to stop trying to recognize sentences.
        ipcMain.on('stopSpeechRecognition', _ => {
          State = 0;  
          console.log("Stopping speech recognition");
          });

        ipcMain.on('startSpeechRecognition', _ => {



          
          
          if (State == -1){
            exec("python3 speech/server_listen.py", (error, stdout, stderr) => {
              if (error) {
                  console.log(`[ERROR] openCashDrawer: ${error.message}`);
                  return;
              }
              
              if (stderr) {
                  console.log(`[STDERROR] openCashDrawer: ${stderr}`);
                  return;
              }
          
              console.log(`openCashDrawer: ${stdout}`); // Output response from the terminal
              });
            }
        


            State = 1;
            Server_socket = new net.Socket();
            Server_socket.connect({ port: Port, host: "localhost" });
            
            // Executed when receiving back data from the server
            Server_socket.on("data", (data) => {
              if (State){
                var s = data.toString("utf-8");
                console.log("received: ", s);
                win.webContents.send('Exectute Command from String', s);
              }
              })

              // This is the command recognized by the python server which tells it to start listening
              Server_socket.write('start and listen!');

            
            console.log("Starting speech recognition");
        });
    }
}


