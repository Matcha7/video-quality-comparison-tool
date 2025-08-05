#!/usr/bin/env python3
"""
Video Quality Comparison Tool
A GUI application for comparing video and audio quality between two sets of files using FFmpeg.
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import subprocess
import threading
import json
import re
import os
from datetime import datetime
from queue import Queue
import sys
import concurrent.futures
from threading import Lock, Event
import time


class VideoComparator:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Video Quality Comparison Tool")
        self.root.geometry("1600x850")
        
        # Video Win Threshold
        self.vmaf_win_threshold = 2.0
        self.ssim_win_threshold = 0.01

        # Audio Win Threshold
        self.psnr_win_threshold = 2.0

        # Data storage
        self.left_files = []
        self.right_files = []
        self.results = {}
        self.running = False
        self.stop_event = Event()
        self.current_metric = tk.StringVar(value="VMAF")
        
        # Threading
        self.log_queue = Queue()
        self.progress_queue = Queue()
        self.worker_thread = None
        self.progress_lock = Lock()
        workers = os.cpu_count() or 5
        self.max_workers = max(1, workers - 4)
        
        # Progress tracking
        self.progress_bars = {}  # row_id -> {"video": progressbar, "audio": progressbar}
        self.score_labels = {}   # row_id -> {"vidleft": label, "vidright": label, "viddiff": label, "audioleft": label, "audioright": label, "audiodiff": label} 

        # Drag and drop state
        self.drag_data = {"active": False, "panel": None, "start_index": None}
        
        # Setup GUI
        self.setup_gui()
        self.check_ffmpeg_availability()
        
        # Start queue processing
        self.process_log_queue()
        self.process_progress_queue()
        
        # Handle window close
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
    
    def setup_gui(self):
        """Initialize the GUI components"""
        # Main container
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        # Configure grid weights
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=1)
        main_frame.columnconfigure(1, weight=1)
        main_frame.columnconfigure(2, weight=2)  # Make progress panel wider
        main_frame.rowconfigure(2, weight=1)
        main_frame.rowconfigure(4, weight=1)
        
        # Left panel
        left_frame = ttk.LabelFrame(main_frame, text="Left Panel", padding="5")
        left_frame.grid(row=0, column=0, rowspan=3, padx=(0, 5), pady=(0, 10), sticky=(tk.W, tk.E, tk.N, tk.S))
        left_frame.columnconfigure(0, weight=1)
        left_frame.rowconfigure(1, weight=1)
        
        # Left add button
        self.left_add_btn = ttk.Button(left_frame, text="Add Files", command=self.add_files_left)
        self.left_add_btn.grid(row=0, column=0, pady=(0, 5), sticky=(tk.W, tk.E))
        
        # Left listbox with scrollbar
        left_list_frame = ttk.Frame(left_frame)
        left_list_frame.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        left_list_frame.columnconfigure(0, weight=1)
        left_list_frame.rowconfigure(0, weight=1)
        
        self.left_listbox = tk.Listbox(left_list_frame, selectmode=tk.SINGLE)
        self.left_listbox.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        left_scrollbar = ttk.Scrollbar(left_list_frame, orient=tk.VERTICAL, command=self.left_listbox.yview)
        left_scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))
        self.left_listbox.configure(yscrollcommand=left_scrollbar.set)
        
        # Right panel
        right_frame = ttk.LabelFrame(main_frame, text="Right Panel", padding="5")
        right_frame.grid(row=0, column=1, rowspan=3, padx=5, pady=(0, 10), sticky=(tk.W, tk.E, tk.N, tk.S))
        right_frame.columnconfigure(0, weight=1)
        right_frame.rowconfigure(1, weight=1)
        
        # Right add button
        self.right_add_btn = ttk.Button(right_frame, text="Add Files", command=self.add_files_right)
        self.right_add_btn.grid(row=0, column=0, pady=(0, 5), sticky=(tk.W, tk.E))
        
        # Right listbox with scrollbar
        right_list_frame = ttk.Frame(right_frame)
        right_list_frame.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        right_list_frame.columnconfigure(0, weight=1)
        right_list_frame.rowconfigure(0, weight=1)
        
        self.right_listbox = tk.Listbox(right_list_frame, selectmode=tk.SINGLE)
        self.right_listbox.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        right_scrollbar = ttk.Scrollbar(right_list_frame, orient=tk.VERTICAL, command=self.right_listbox.yview)
        right_scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))
        self.right_listbox.configure(yscrollcommand=right_scrollbar.set)
        
        # Progress panel
        progress_frame = ttk.LabelFrame(main_frame, text="Progress & Results", padding="5")
        progress_frame.grid(row=0, column=2, rowspan=3, padx=(5, 0), pady=(0, 10), sticky=(tk.W, tk.E, tk.N, tk.S))
        progress_frame.columnconfigure(0, weight=1)
        progress_frame.rowconfigure(0, weight=1)
        
        # Progress canvas with scrollbar
        self.progress_canvas = tk.Canvas(progress_frame)
        progress_scrollbar = ttk.Scrollbar(progress_frame, orient=tk.VERTICAL, command=self.progress_canvas.yview)
        self.progress_scrollable_frame = ttk.Frame(self.progress_canvas)
        
        self.progress_scrollable_frame.bind(
            "<Configure>",
            lambda e: self.progress_canvas.configure(scrollregion=self.progress_canvas.bbox("all"))
        )
        
        self.progress_canvas.create_window((0, 0), window=self.progress_scrollable_frame, anchor="nw")
        self.progress_canvas.configure(yscrollcommand=progress_scrollbar.set)
        
        self.progress_canvas.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        progress_scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))
        
        # Control panel
        control_frame = ttk.Frame(main_frame)
        control_frame.grid(row=3, column=0, columnspan=3, pady=10, sticky=(tk.W, tk.E))
        control_frame.columnconfigure(4, weight=1)
        
        # Metric selector
        ttk.Label(control_frame, text="Video Metric:").grid(row=0, column=0, padx=(0, 5))
        metric_combo = ttk.Combobox(control_frame, textvariable=self.current_metric, 
                                   values=["VMAF", "SSIM"], state="readonly", width=10)
        metric_combo.grid(row=0, column=1, padx=(0, 20))
        
        # Clear all button
        self.clear_all_btn = ttk.Button(control_frame, text="Clear All", command=self.clear_all_files)
        self.clear_all_btn.grid(row=0, column=2, padx=(0, 10))
        
        # Start button
        self.start_btn = ttk.Button(control_frame, text="Start Comparison", command=self.start_comparison)
        self.start_btn.grid(row=0, column=3, padx=(0, 10))
        
        # Stop button
        self.stop_btn = ttk.Button(control_frame, text="Stop", command=self.stop_comparison, state="disabled")
        self.stop_btn.grid(row=0, column=4, padx=(0, 10))
        
        # Exit button
        self.exit_btn = ttk.Button(control_frame, text="Exit", command=self.on_closing)
        self.exit_btn.grid(row=0, column=5, sticky=tk.E)
        
        # Console
        console_frame = ttk.LabelFrame(main_frame, text="Console", padding="5")
        console_frame.grid(row=4, column=0, columnspan=3, sticky=(tk.W, tk.E, tk.N, tk.S))
        console_frame.columnconfigure(0, weight=1)
        console_frame.rowconfigure(0, weight=1)
        
        self.console = scrolledtext.ScrolledText(console_frame, height=8, state=tk.DISABLED)
        self.console.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        # Console context menu
        self.console_menu = tk.Menu(self.console, tearoff=0)
        self.console_menu.add_command(label="Copy All", command=self.copy_console_content)
        self.console_menu.add_command(label="Clear", command=self.clear_console)
        self.console.bind("<Button-3>", self.show_console_menu)
        
        # Setup drag and drop
        self.setup_drag_drop()
        
        # Setup context menus for file removal
        self.setup_context_menus()
    
    def setup_drag_drop(self):
        """Setup drag and drop functionality for both listboxes"""
        # Left listbox
        self.left_listbox.bind("<Button-1>", lambda e: self.on_drag_start(e, "left"))
        self.left_listbox.bind("<B1-Motion>", lambda e: self.on_drag_motion(e, "left"))
        self.left_listbox.bind("<ButtonRelease-1>", lambda e: self.on_drag_release(e, "left"))
        
        # Right listbox
        self.right_listbox.bind("<Button-1>", lambda e: self.on_drag_start(e, "right"))
        self.right_listbox.bind("<B1-Motion>", lambda e: self.on_drag_motion(e, "right"))
        self.right_listbox.bind("<ButtonRelease-1>", lambda e: self.on_drag_release(e, "right"))
    
    def setup_context_menus(self):
        """Setup context menus for file removal"""
        # Left listbox menu
        self.left_menu = tk.Menu(self.left_listbox, tearoff=0)
        self.left_menu.add_command(label="Remove", command=lambda: self.remove_selected_file("left"))
        self.left_listbox.bind("<Button-3>", lambda e: self.show_file_menu(e, "left"))
        
        # Right listbox menu
        self.right_menu = tk.Menu(self.right_listbox, tearoff=0)
        self.right_menu.add_command(label="Remove", command=lambda: self.remove_selected_file("right"))
        self.right_listbox.bind("<Button-3>", lambda e: self.show_file_menu(e, "right"))
    
    def on_drag_start(self, event, panel):
        """Handle drag start event"""
        listbox = self.left_listbox if panel == "left" else self.right_listbox
        index = listbox.nearest(event.y)
        if index >= 0 and index < listbox.size():
            self.drag_data = {
                "active": True,
                "panel": panel,
                "start_index": index
            }
            listbox.selection_clear(0, tk.END)
            listbox.selection_set(index)
    
    def on_drag_motion(self, event, panel):
        """Handle drag motion event"""
        if not self.drag_data["active"] or self.drag_data["panel"] != panel:
            return
        
        listbox = self.left_listbox if panel == "left" else self.right_listbox
        index = listbox.nearest(event.y)
        if index >= 0 and index < listbox.size():
            listbox.selection_clear(0, tk.END)
            listbox.selection_set(index)
    
    def on_drag_release(self, event, panel):
        """Handle drag release event"""
        if not self.drag_data["active"] or self.drag_data["panel"] != panel:
            return
        
        listbox = self.left_listbox if panel == "left" else self.right_listbox
        end_index = listbox.nearest(event.y)
        start_index = self.drag_data["start_index"]
        
        if end_index >= 0 and end_index < listbox.size() and start_index != end_index:
            self.reorder_files(panel, start_index, end_index)
        
        self.drag_data = {"active": False, "panel": None, "start_index": None}
    
    def reorder_files(self, panel, old_index, new_index):
        """Reorder files in the specified panel"""
        file_list = self.left_files if panel == "left" else self.right_files
        
        if 0 <= old_index < len(file_list) and 0 <= new_index < len(file_list):
            # Move the item
            item = file_list.pop(old_index)
            file_list.insert(new_index, item)
            
            # Clear results and progress bars since order changed
            self.results.clear()
            self.clear_progress_bars()
            
            # Refresh display
            self.refresh_file_display("left")
            self.refresh_file_display("right")
            self.setup_progress_bars()
            
            # Select the moved item
            listbox = self.left_listbox if panel == "left" else self.right_listbox
            listbox.selection_clear(0, tk.END)
            listbox.selection_set(new_index)
    
    def add_files_left(self):
        """Add files to left panel"""
        self.add_files("left")
    
    def add_files_right(self):
        """Add files to right panel"""
        self.add_files("right")
    
    def add_files(self, panel):
        """Add files to specified panel"""
        files = filedialog.askopenfilenames(
            title=f"Select files for {panel} panel",
            filetypes=[
                ("Video files", "*.mp4 *.avi *.mkv *.mov *.wmv *.flv *.webm"),
                ("All files", "*.*")
            ]
        )
        
        if files:
            file_list = self.left_files if panel == "left" else self.right_files
            file_list.extend(files)
            self.refresh_file_display(panel)
            self.setup_progress_bars()
            self.log_message("INFO", f"Added {len(files)} files to {panel} panel")
    
    def remove_selected_file(self, panel):
        """Remove selected file from specified panel"""
        listbox = self.left_listbox if panel == "left" else self.right_listbox
        file_list = self.left_files if panel == "left" else self.right_files
        
        selection = listbox.curselection()
        if selection:
            index = selection[0]
            if 0 <= index < len(file_list):
                removed_file = file_list.pop(index)
                
                # Clear results and progress bars since files changed
                self.results.clear()
                self.clear_progress_bars()
                
                self.refresh_file_display(panel)
                self.setup_progress_bars()
                self.log_message("INFO", f"Removed file: {os.path.basename(removed_file)}")
    
    def clear_all_files(self):
        """Clear all files from both panels"""
        if not self.left_files and not self.right_files:
            return
        
        # Confirm if there are files to clear
        if messagebox.askyesno("Clear All Files", "Are you sure you want to remove all files from both panels?"):
            self.left_files.clear()
            self.right_files.clear()
            self.results.clear()
            self.clear_progress_bars()
            
            self.refresh_file_display("left")
            self.refresh_file_display("right")
            self.log_message("INFO", "All files cleared from both panels")
    
    def get_total_frames(self, video_path):
        cmd = [
            "ffprobe",
            "-v", "error",
            "-count_frames",
            "-select_streams", "v:0",
            "-show_entries", "stream=nb_read_frames",
            "-of", "default=nokey=1:noprint_wrappers=1",
            video_path
        ]
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        return int(result.stdout.strip()) if result.stdout.strip().isdigit() else None

    def show_file_menu(self, event, panel):
        """Show context menu for file operations"""
        listbox = self.left_listbox if panel == "left" else self.right_listbox
        menu = self.left_menu if panel == "left" else self.right_menu
        
        # Select item under cursor
        index = listbox.nearest(event.y)
        if index >= 0 and index < listbox.size():
            listbox.selection_clear(0, tk.END)
            listbox.selection_set(index)
            menu.post(event.x_root, event.y_root)
    
    def show_console_menu(self, event):
        """Show console context menu"""
        self.console_menu.post(event.x_root, event.y_root)
    
    def refresh_file_display(self, panel):
        """Refresh the file display for specified panel"""
        listbox = self.left_listbox if panel == "left" else self.right_listbox
        file_list = self.left_files if panel == "left" else self.right_files
        
        listbox.delete(0, tk.END)
        for i, file_path in enumerate(file_list):
            display_name = os.path.basename(file_path)
            
            # Add result indicators if available - using text instead of emoji
            if f"row_{i}" in self.results:
                result = self.results[f"row_{i}"]
                video_indicator = ""
                audio_indicator = ""
                
                if result.get("video_winner") == panel:
                    video_indicator = "[V] "  # Video winner
                if result.get("audio_winner") == panel:
                    audio_indicator = "[A] "  # Audio winner
                
                display_name = f"{video_indicator}{audio_indicator}{display_name}"
            
            listbox.insert(tk.END, display_name)
    
    def setup_progress_bars(self):
        """Setup progress bars and score displays for each row"""
        self.clear_progress_bars()
        
        min_count = min(len(self.left_files), len(self.right_files))
        if min_count == 0:
            return
        
        for i in range(min_count):
            row_frame = ttk.Frame(self.progress_scrollable_frame)
            row_frame.grid(row=i, column=0, sticky=(tk.W, tk.E), padx=5, pady=4)
            row_frame.columnconfigure(1, weight=1)
            row_frame.columnconfigure(3, weight=1)
            
            # Row label
            ttk.Label(row_frame, text=f"Row {i+1}:", font=("TkDefaultFont", 9, "bold")).grid(row=0, column=0, padx=(0, 10), sticky=tk.W)
            
            # Video progress
            ttk.Label(row_frame, text="Video", foreground="green").grid(row=0, column=1, sticky=tk.W)
            video_progress = ttk.Progressbar(row_frame, length=120, mode='determinate')
            video_progress.grid(row=0, column=2, padx=5)
            
            # Audio progress
            ttk.Label(row_frame, text="Audio", foreground="blue").grid(row=0, column=3, sticky=tk.W)
            audio_progress = ttk.Progressbar(row_frame, length=120, mode='determinate')
            audio_progress.grid(row=0, column=4, padx=5)
            
            # Score display frame
            score_frame = ttk.Frame(row_frame)
            score_frame.grid(row=1, column=0, columnspan=5, sticky=(tk.W, tk.E), pady=(2, 0))
            score_frame.columnconfigure(1, weight=1)
            
            # Vid Left score label
            vid_left_score_label = ttk.Label(score_frame, text="Visual Score (L): --", foreground="gray", font=("TkDefaultFont", 8))
            vid_left_score_label.grid(row=0, column=0, padx=(0, 10), sticky=tk.W)
            
            # Vid Difference label (center)
            vid_diff_label = ttk.Label(score_frame, text="", foreground="purple", font=("TkDefaultFont", 8, "bold"))
            vid_diff_label.grid(row=0, column=1, sticky=tk.N)
            
            # Vid Right score label
            vid_right_score_label = ttk.Label(score_frame, text="Visual Score (R): --", foreground="gray", font=("TkDefaultFont", 8))
            vid_right_score_label.grid(row=0, column=2, padx=(10, 0), sticky=tk.E)


            # Audio Left score label
            audio_left_score_label = ttk.Label(score_frame, text="Audio Score (L): --", foreground="gray", font=("TkDefaultFont", 8))
            audio_left_score_label.grid(row=1, column=0, padx=(0, 10), sticky=tk.W)
            
            # Audio Difference label (center)
            audio_diff_label = ttk.Label(score_frame, text="", foreground="purple", font=("TkDefaultFont", 8, "bold"))
            audio_diff_label.grid(row=1, column=1, sticky=tk.N)
            
            # Audio Right score label
            audio_right_score_label = ttk.Label(score_frame, text="Audio Score (R): --", foreground="gray", font=("TkDefaultFont", 8))
            audio_right_score_label.grid(row=1, column=2, padx=(10, 0), sticky=tk.E)
            

            self.progress_bars[f"row_{i}"] = {
                "video": video_progress,
                "audio": audio_progress,
                "frame": row_frame
            }
            
            self.score_labels[f"row_{i}"] = {
                "vidleft": vid_left_score_label,
                "vidright": vid_right_score_label,
                "viddiff": vid_diff_label,
                "audioleft": audio_left_score_label,
                "audioright": audio_right_score_label,
                "audiodiff": audio_diff_label
            }
        
        # Update canvas scroll region
        self.progress_scrollable_frame.update_idletasks()
        self.progress_canvas.configure(scrollregion=self.progress_canvas.bbox("all"))
    
    def clear_progress_bars(self):
        """Clear all progress bars and score labels"""
        for row_id, bars in self.progress_bars.items():
            bars["frame"].destroy()
        self.progress_bars.clear()
        self.score_labels.clear()
    
    def update_progress(self, row_id, progress_type, value):
        """Update progress bar value"""
        self.progress_queue.put((row_id, progress_type, value))
    
    def process_progress_queue(self):
        """Process progress updates from queue"""
        try:
            while not self.progress_queue.empty():
                row_id, progress_type, value = self.progress_queue.get_nowait()
                with self.progress_lock:
                    if row_id in self.progress_bars and progress_type in self.progress_bars[row_id]:
                        self.progress_bars[row_id][progress_type].configure(value=value)
        except:
            pass
        
        # Schedule next check
        self.root.after(50, self.process_progress_queue)
    
    def update_score_display(self, row_id, vid_left_score, vid_right_score, audio_left_score, audio_right_score, metric):
        """Update score display for a row"""
        if row_id not in self.score_labels:
            return
        
        def update_labels():
            try:
                labels = self.score_labels[row_id]
                
                ## Video

                # Update individual scores
                labels["vidleft"].configure(text=f"Left: {vid_left_score:.2f}")
                labels["vidright"].configure(text=f"Right: {vid_right_score:.2f}")
                
                # Calculate and display difference
                diff = abs(vid_left_score - vid_right_score)
                winner = "Left" if vid_left_score > vid_right_score else "Right" if vid_right_score > vid_left_score else "Tie"
                
                if diff < (self.vmaf_win_threshold if metric == "VMAF" else self.ssim_win_threshold):
                    diff_text = "≈ Tie"
                    diff_color = "gray"
                else:
                    diff_text = f"{winner} +{diff:.2f}"
                    diff_color = "green" if winner == "Left" else "red"
                
                labels["viddiff"].configure(text=diff_text, foreground=diff_color)
                
                # Update colors based on winner
                if vid_left_score > vid_right_score and diff >= (self.vmaf_win_threshold if metric == "VMAF" else self.ssim_win_threshold):
                    labels["vidleft"].configure(foreground="green")
                    labels["vidright"].configure(foreground="gray")
                elif vid_right_score > vid_left_score and diff >= (self.vmaf_win_threshold if metric == "VMAF" else self.ssim_win_threshold):
                    labels["vidleft"].configure(foreground="gray")
                    labels["vidright"].configure(foreground="red")
                else:
                    labels["vidleft"].configure(foreground="gray")
                    labels["vidright"].configure(foreground="gray")

                ## Audio

                # Update individual scores
                labels["audioleft"].configure(text=f"Left: {audio_left_score:.2f}")
                labels["audioright"].configure(text=f"Right: {audio_right_score:.2f}")
                
                # Calculate and display difference
                diff = abs(audio_left_score - audio_right_score)
                winner = "Left" if audio_left_score > audio_right_score else "Right" if audio_right_score > audio_left_score else "Tie"
                
                if diff < (self.psnr_win_threshold):
                    diff_text = "≈ Tie"
                    diff_color = "gray"
                else:
                    diff_text = f"{winner} +{diff:.2f}"
                    diff_color = "green" if winner == "Left" else "red"
                
                labels["audiodiff"].configure(text=diff_text, foreground=diff_color)
                
                # Update colors based on winner
                if audio_left_score > audio_right_score and diff >= self.psnr_win_threshold:
                    labels["audioleft"].configure(foreground="green")
                    labels["audioright"].configure(foreground="gray")
                elif audio_right_score > audio_left_score and diff >= self.psnr_win_threshold:
                    labels["audioleft"].configure(foreground="gray")
                    labels["audioright"].configure(foreground="red")
                else:
                    labels["audioleft"].configure(foreground="gray")
                    labels["audioright"].configure(foreground="gray")
                    
            except Exception as e:
                print(f"Error updating score display: {e}")
        
        self.root.after(0, update_labels)
    
    def check_ffmpeg_availability(self):
        """Check if FFmpeg is available"""
        try:
            result = subprocess.run(
                ["ffmpeg", "-version"],
                capture_output=True,
                text=True,
                timeout=10,
                encoding='utf-8',
                errors='replace'
            )
            if result.returncode == 0:
                self.log_message("INFO", "FFmpeg is available")
                return True
        except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
            pass
        
        self.log_message("ERROR", "FFmpeg not found. Please install FFmpeg and ensure it's in your PATH.")
        self.start_btn.configure(state="disabled")
        messagebox.showerror(
            "FFmpeg Not Found",
            "FFmpeg is required for this application.\nPlease install FFmpeg and ensure it's accessible from the command line."
        )
        return False
    
    def start_comparison(self):
        """Start the comparison process"""
        if self.running:
            return
        
        if not self.left_files or not self.right_files:
            messagebox.showwarning("No Files", "Please add files to both panels before starting comparison.")
            return
        
        # Clear previous results
        self.results.clear()
        self.refresh_file_display("left")
        self.refresh_file_display("right")
        self.setup_progress_bars()
        
        self.running = True
        self.stop_event.clear()
        self.start_btn.configure(text="Running...", state="disabled")
        self.stop_btn.configure(state="normal")
        self.log_message("INFO", f"Starting comparison with {self.current_metric.get()} metric using {self.max_workers} workers")
        
        # Start worker thread
        self.worker_thread = threading.Thread(target=self.run_comparisons, daemon=True)
        self.worker_thread.start()
    
    def stop_comparison(self):
        """Stop the comparison process"""
        if not self.running:
            return
        
        self.log_message("INFO", "Stopping comparison...")
        self.stop_event.set()
        self.running = False
        
        # Update UI immediately
        self.start_btn.configure(text="Start Comparison", state="normal")
        self.stop_btn.configure(state="disabled")
    
    def run_comparisons(self):
        """Run all comparisons using multithreading"""
        try:
            min_count = min(len(self.left_files), len(self.right_files))
            
            # Create list of comparison tasks
            tasks = []
            for i in range(min_count):
                tasks.append((i, self.left_files[i], self.right_files[i]))
            
            # Use ThreadPoolExecutor for parallel processing
            with concurrent.futures.ThreadPoolExecutor(max_workers=self.max_workers) as executor:
                # Submit all tasks
                future_to_row = {}
                for row_idx, left_file, right_file in tasks:
                    if self.stop_event.is_set():
                        break
                    
                    future = executor.submit(self.compare_row, row_idx, left_file, right_file)
                    future_to_row[future] = row_idx
                
                # Process completed tasks
                for future in concurrent.futures.as_completed(future_to_row):
                    if self.stop_event.is_set():
                        break
                    
                    row_idx = future_to_row[future]
                    try:
                        result = future.result()
                        if result:
                            self.results[f"row_{row_idx}"] = result
                            
                            # Update display and scores
                            self.root.after(0, lambda: self.refresh_file_display("left"))
                            self.root.after(0, lambda: self.refresh_file_display("right"))
                            
                            # Update score display
                            self.update_score_display(
                                f"row_{row_idx}",
                                result.get("video_score_left", 0),
                                result.get("video_score_right", 0),
                                result.get("audio_score_left", 0),
                                result.get("audio_score_right", 0),
                                self.current_metric.get()
                            )
                    
                    except Exception as e:
                        self.log_queue.put(("ERROR", f"Row {row_idx + 1} comparison failed: {str(e)}"))
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Comparison process failed: {str(e)}"))
        
        finally:
            # Reset UI state
            self.running = False
            if self.stop_event.is_set():
                self.log_queue.put(("INFO", "Comparison stopped by user"))
            else:
                self.log_queue.put(("INFO", "All comparisons completed"))
            
            self.root.after(0, lambda: self.start_btn.configure(text="Start Comparison", state="normal"))
            self.root.after(0, lambda: self.stop_btn.configure(state="disabled"))
    
    def compare_row(self, row_idx, left_file, right_file):
        """Compare a single row (video and audio)"""
        try:
            if self.stop_event.is_set():
                return None
            
            row_id = f"row_{row_idx}"
            self.log_queue.put(("INFO", f"Starting row {row_idx + 1}: {os.path.basename(left_file)} vs {os.path.basename(right_file)}"))
            
            # Video comparison
            self.update_progress(row_id, "video", 0)
            video_result = self.run_video_comparison(left_file, right_file, self.current_metric.get(), row_idx)
            if self.stop_event.is_set():
                return None
            self.update_progress(row_id, "video", 100)
            
            # Audio comparison
            self.update_progress(row_id, "audio", 0)
            audio_result = self.run_audio_comparison(left_file, right_file, row_idx)
            if self.stop_event.is_set():
                return None
            self.update_progress(row_id, "audio", 100)
            
            self.log_queue.put(("INFO", f"Completed row {row_idx + 1}"))
            
            return {
                "video_winner": video_result.get("winner", "tie"),
                "audio_winner": audio_result.get("winner", "tie"),
                "video_score_left": video_result.get("left_score", 0),
                "video_score_right": video_result.get("right_score", 0),
                "audio_score_left": audio_result.get("left_score", 0),
                "audio_score_right": audio_result.get("right_score", 0)
            }
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1} comparison error: {str(e)}"))
            return None
    
    def run_video_comparison(self, left_file, right_file, metric, row_idx):
        """Run video quality comparison using FFmpeg with bidirectional analysis"""
        try:
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            # First comparison: left as reference, right as distorted
            self.log_queue.put(("INFO", f"Row {row_idx + 1}: Running {metric} with left as reference..."))
            self.update_progress(f"row_{row_idx}", "video", 10)
            left_as_ref_score = self.run_single_video_comparison(left_file, right_file, metric, "left_ref", row_idx)
            
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            # Update progress
            self.update_progress(f"row_{row_idx}", "video", 55)
            
            # Second comparison: right as reference, left as distorted
            self.log_queue.put(("INFO", f"Row {row_idx + 1}: Running {metric} with right as reference..."))
            right_as_ref_score = self.run_single_video_comparison(right_file, left_file, metric, "right_ref", row_idx)
            
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            self.update_progress(f"row_{row_idx}", "video", 100)
            
            # Determine winner based on both scores
            return self.determine_video_winner(left_as_ref_score, right_as_ref_score, metric, row_idx)
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Video comparison error: {str(e)}"))
            return {"winner": "tie", "left_score": 0, "right_score": 0}
    
    def run_single_video_comparison(self, reference_file, distorted_file, metric, comparison_type, row_idx):
        """Run a single video comparison with specified reference"""
        try:
            if self.stop_event.is_set():
                return None
            
            if metric == "VMAF":
                cmd = [
                    "ffmpeg", "-i", reference_file, "-i", distorted_file,
                    "-lavfi", "libvmaf=log_fmt=json",
                    "-f", "null", "-"
                ]
            else:  # SSIM
                cmd = [
                    "ffmpeg", "-i", reference_file, "-i", distorted_file,
                    "-lavfi", "ssim",
                    "-f", "null", "-"
                ]
            
            total_frames = max(1, self.get_total_frames(reference_file) or 0)

            # Run process with progress monitoring
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding='utf-8',
                errors='replace'
            )
            
            # Monitor process progress
            stderr_output = ""
            while True:
                if self.stop_event.is_set():
                    process.terminate()
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        process.kill()
                    return None
                
                output = process.stderr.readline()
                if output == '' and process.poll() is not None:
                    break
                if output:
                    stderr_output += output
                    # Try to extract progress information from FFmpeg output
                    self.extract_ffmpeg_progress(output, row_idx, "video", comparison_type, total_frames)
                
                time.sleep(0.1)  # Small delay to prevent excessive CPU usage
            
            # Get remaining output
            remaining_stderr = process.stderr.read()
            stderr_output += remaining_stderr
            
            if process.returncode != 0:
                error_msg = stderr_output.strip() if stderr_output else "Unknown FFmpeg error"
                self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Video comparison failed ({comparison_type}): {error_msg}"))
                return None
            
            return self.parse_single_video_output(stderr_output, metric, comparison_type, row_idx)
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Single video comparison error ({comparison_type}): {str(e)}"))
            return None
    
    def extract_ffmpeg_progress(self, output_line, row_idx, media_type, comparison_type, total_frames):
        """Extract progress information from FFmpeg output"""
        try:
            # Look for time progress in FFmpeg output
            frame_match = re.search(r'frame=\s*(\d+)', output_line)
            if frame_match:
                curr_frame = int(frame_match.group(1))
                
                if curr_frame > 0:
                    # Estimate progress - this is rough and could be improved
                    # by getting actual duration first
                    base_progress = 10 if comparison_type == "left_ref" else 55
                    additional_progress = int(min(1, (curr_frame/total_frames))*45)
                    
                    if media_type == "video":
                        self.update_progress(f"row_{row_idx}", "video", base_progress + additional_progress)
                    
        except:
            pass  # Ignore parsing errors
    
    def run_audio_comparison(self, left_file, right_file, row_idx):
        """Run audio quality comparison using FFmpeg with bidirectional PSNR analysis"""
        try:
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            # First comparison: left as reference, right as distorted
            self.log_queue.put(("INFO", f"Row {row_idx + 1}: Running audio PSNR with left as reference..."))
            self.update_progress(f"row_{row_idx}", "audio", 25)
            left_as_ref_score = self.run_single_audio_comparison(left_file, right_file, "left_ref", row_idx)
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            self.update_progress(f"row_{row_idx}", "audio", 50)
            
            # Second comparison: right as reference, left as distorted  
            self.log_queue.put(("INFO", f"Row {row_idx + 1}: Running audio PSNR with right as reference..."))
            right_as_ref_score = self.run_single_audio_comparison(right_file, left_file, "right_ref", row_idx)
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            self.update_progress(f"row_{row_idx}", "audio", 75)
            
            # Determine winner based on both scores
            return self.determine_audio_winner(left_as_ref_score, right_as_ref_score, row_idx)
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Audio comparison error: {str(e)}"))
            return {"winner": "tie", "left_score": 0, "right_score": 0}
    
    def run_single_audio_comparison(self, reference_file, distorted_file, comparison_type, row_idx):
        """Run a single audio PSNR comparison with specified reference"""
        try:
            if self.stop_event.is_set():
                return None
            
            cmd = [
                "ffmpeg", "-i", reference_file, "-i", distorted_file,
                "-lavfi", "[0:a][1:a]apsnr",
                "-f", "null", "-"
            ]
            
            # Run process with progress monitoring
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding='utf-8',
                errors='replace'
            )
            
            # Monitor process progress
            stderr_output = ""
            while True:
                if self.stop_event.is_set():
                    process.terminate()
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        process.kill()
                    return None
                
                output = process.stderr.readline()
                if output == '' and process.poll() is not None:
                    break
                if output:
                    stderr_output += output
                
                time.sleep(0.1)  # Small delay to prevent excessive CPU usage
            
            # Get remaining output
            remaining_stderr = process.stderr.read()
            stderr_output += remaining_stderr
            
            if process.returncode != 0:
                error_msg = stderr_output.strip() if stderr_output else "Unknown FFmpeg error"
                self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Audio PSNR failed ({comparison_type}): {error_msg}"))
                return None
            
            return self.parse_single_audio_output(stderr_output, comparison_type, row_idx)
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Single audio comparison error ({comparison_type}): {str(e)}"))
            return None
    
    def determine_video_winner(self, left_as_ref_score, right_as_ref_score, metric, row_idx):
        """Determine video quality winner based on bidirectional comparison"""
        try:
            if left_as_ref_score is None or right_as_ref_score is None:
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            if metric == "VMAF":
                # For VMAF, higher score means better quality
                # left_as_ref_score: how good right looks compared to left
                # right_as_ref_score: how good left looks compared to right
                
                # If right scores high when left is reference, right is close to left quality
                # If left scores high when right is reference, left is close to right quality
                # The one with higher "when used as distorted" score is likely better
                
                left_quality = left_as_ref_score
                right_quality = right_as_ref_score
                
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: VMAF results - Left quality: {left_quality:.2f}, Right quality: {right_quality:.2f}"))
                
                if abs(left_quality - right_quality) < self.vmaf_win_threshold:  # Very close scores
                    winner = "tie"
                elif left_quality > right_quality:
                    winner = "left"
                else:
                    winner = "right"
                
                return {
                    "winner": winner,
                    "left_score": left_quality,
                    "right_score": right_quality
                }
            
            else:  # SSIM
                # For SSIM, higher score (closer to 1.0) means better similarity/quality
                left_quality = left_as_ref_score
                right_quality = right_as_ref_score
                
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: SSIM results - Left quality: {left_quality:.4f}, Right quality: {right_quality:.4f}"))
                
                if abs(left_quality - right_quality) < self.ssim_win_threshold:  # Very close scores
                    winner = "tie"
                elif left_quality > right_quality:
                    winner = "left"
                else:
                    winner = "right"
                
                return {
                    "winner": winner,
                    "left_score": left_quality,
                    "right_score": right_quality
                }
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Error determining video winner: {str(e)}"))
            return {"winner": "tie", "left_score": 0, "right_score": 0}
    
    def determine_audio_winner(self, left_as_ref_score, right_as_ref_score, row_idx):
        """Determine audio quality winner based on bidirectional PSNR comparison"""
        try:
            if left_as_ref_score is None or right_as_ref_score is None:
                # Fallback to individual audio analysis if PSNR fails
                return self.run_audio_analysis_fallback(self.left_files[row_idx], self.right_files[row_idx], row_idx)
            
            # For PSNR, higher score means better quality
            # left_as_ref_score: how good right sounds compared to left
            # right_as_ref_score: how good left sounds compared to right
            
            left_quality = left_as_ref_score
            right_quality = right_as_ref_score
            
            self.log_queue.put(("INFO", f"Row {row_idx + 1}: Audio PSNR results - Left quality: {left_quality:.2f} dB, Right quality: {right_quality:.2f} dB"))
            
            if abs(left_quality - right_quality) < 1.0:  # Within 1 dB difference
                winner = "tie"
            elif left_quality > right_quality:
                winner = "left"
            else:
                winner = "right"
            
            return {
                "winner": winner,
                "left_score": left_quality,
                "right_score": right_quality
            }
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Error determining audio winner: {str(e)}"))
            return {"winner": "tie", "left_score": 0, "right_score": 0}
    
    def run_audio_analysis_fallback(self, left_file, right_file, row_idx):
        """Fallback audio analysis using EBU R128"""
        try:
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            left_loudness = self.get_audio_loudness(left_file, row_idx)
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            right_loudness = self.get_audio_loudness(right_file, row_idx)
            if self.stop_event.is_set():
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            if left_loudness is None or right_loudness is None:
                return {"winner": "tie", "left_score": 0, "right_score": 0}
            
            # Higher (less negative) loudness is generally better for most content
            winner = "left" if left_loudness > right_loudness else "right"
            if abs(left_loudness - right_loudness) < 1.0:  # Within 1 LUFS
                winner = "tie"
            
            self.log_queue.put(("INFO", f"Row {row_idx + 1}: Audio loudness - Left: {left_loudness:.1f} LUFS, Right: {right_loudness:.1f} LUFS"))
            
            return {
                "winner": winner,
                "left_score": left_loudness,
                "right_score": right_loudness
            }
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Audio analysis fallback error: {str(e)}"))
            return {"winner": "tie", "left_score": 0, "right_score": 0}
    
    def get_audio_loudness(self, file_path, row_idx):
        """Get audio loudness using EBU R128"""
        try:
            if self.stop_event.is_set():
                return None
            
            cmd = [
                "ffmpeg", "-i", file_path,
                "-af", "ebur128=peak=true",
                "-f", "null", "-"
            ]
            
            # Run process with monitoring for stop event
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding='utf-8',
                errors='replace'
            )
            
            stderr_output = ""
            while True:
                if self.stop_event.is_set():
                    process.terminate()
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        process.kill()
                    return None
                
                output = process.stderr.readline()
                if output == '' and process.poll() is not None:
                    break
                if output:
                    stderr_output += output
                
                time.sleep(0.1)
            
            # Get remaining output
            remaining_stderr = process.stderr.read()
            stderr_output += remaining_stderr
            
            # Parse integrated loudness from output
            for line in stderr_output.split('\n'):
                if 'Integrated loudness:' in line:
                    match = re.search(r'Integrated loudness:\s*(-?\d+\.?\d*)\s*LUFS', line)
                    if match:
                        return float(match.group(1))
            
            return None
        
        except Exception:
            return None
    
    def parse_single_video_output(self, output, metric, comparison_type, row_idx):
        """Parse single video comparison output"""
        try:
            if metric == "VMAF":
                return self.parse_single_vmaf_output(output, comparison_type, row_idx)
            else:  # SSIM
                return self.parse_single_ssim_output(output, comparison_type, row_idx)
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Failed to parse {metric} output ({comparison_type}): {str(e)}"))
            return None
    
    def parse_single_vmaf_output(self, output, comparison_type, row_idx):
        """Parse single VMAF output"""
        try:
            # Look for VMAF score in the output
            vmaf_match = re.search(r'VMAF score:\s*([0-9.]+)', output)
            if vmaf_match:
                score = float(vmaf_match.group(1))
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: VMAF score ({comparison_type}): {score:.2f}"))
                return score
            
            # Alternative parsing for different VMAF output formats
            vmaf_matches = re.findall(r'VMAF.*?([0-9.]+)', output)
            if vmaf_matches:
                score = float(vmaf_matches[-1])  # Take the last (usually average) score
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: VMAF score ({comparison_type}): {score:.2f}"))
                return score
            
            self.log_queue.put(("WARNING", f"Row {row_idx + 1}: Could not parse VMAF score from output ({comparison_type})"))
            return None
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Error parsing VMAF output ({comparison_type}): {str(e)}"))
            return None
    
    def parse_single_ssim_output(self, output, comparison_type, row_idx):
        """Parse single SSIM output"""
        try:
            # Look for SSIM mean/average values in the stats output
            # SSIM stats typically show: n:1 Y:0.123456 U:0.234567 V:0.345678 All:0.456789 (12.345678)
            ssim_match = re.search(r'All:([0-9.]+)', output)
            if ssim_match:
                score = float(ssim_match.group(1))
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: SSIM score ({comparison_type}): {score:.4f}"))
                return score
            
            # Alternative parsing - look for SSIM values in different formats
            # Sometimes appears as "SSIM Y:x.xxx U:x.xxx V:x.xxx All:x.xxx"
            ssim_all_match = re.search(r'SSIM.*?All:([0-9.]+)', output)
            if ssim_all_match:
                score = float(ssim_all_match.group(1))
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: SSIM score ({comparison_type}): {score:.4f}"))
                return score
            
            # Look for the last line that contains SSIM stats
            lines = output.strip().split('\n')
            for line in reversed(lines):
                if 'All:' in line and ('Y:' in line or 'SSIM' in line):
                    all_match = re.search(r'All:([0-9.]+)', line)
                    if all_match:
                        score = float(all_match.group(1))
                        self.log_queue.put(("INFO", f"Row {row_idx + 1}: SSIM score ({comparison_type}): {score:.4f}"))
                        return score
            
            # If no "All:" found, try to get Y channel value as fallback
            y_match = re.search(r'Y:([0-9.]+)', output)
            if y_match:
                score = float(y_match.group(1))
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: SSIM Y-channel score ({comparison_type}): {score:.4f}"))
                return score
            
            self.log_queue.put(("WARNING", f"Row {row_idx + 1}: Could not parse SSIM score from output ({comparison_type})"))
            self.log_queue.put(("DEBUG", f"Row {row_idx + 1}: SSIM output sample: {output[-200:]}"))  # Log last 200 chars for debugging
            return None
        
        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Error parsing SSIM output ({comparison_type}): {str(e)}"))
            return None
    
    def parse_single_audio_output(self, output, comparison_type, row_idx):
        try:
            psnr_match = re.search(r'PSNR\s+ch0:\s*([0-9.]+)', output)
            if psnr_match:
                score = float(psnr_match.group(1))
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: Audio PSNR score ({comparison_type}): {score:.2f} dB"))
                return score

            psnr_matches = re.findall(r'([0-9.]+)\s*dB', output)
            if psnr_matches:
                score = float(psnr_matches[-1])
                self.log_queue.put(("INFO", f"Row {row_idx + 1}: Audio PSNR score ({comparison_type}): {score:.2f} dB"))
                return score

            self.log_queue.put(("WARNING", f"Row {row_idx + 1}: Could not parse audio PSNR score from output ({comparison_type})"))
            return None

        except Exception as e:
            self.log_queue.put(("ERROR", f"Row {row_idx + 1}: Error parsing audio PSNR output ({comparison_type}): {str(e)}"))
            return None
    
    def process_log_queue(self):
        """Process log messages from queue"""
        try:
            while not self.log_queue.empty():
                level, message = self.log_queue.get_nowait()
                self.log_message(level, message)
        except:
            pass
        
        # Schedule next check
        self.root.after(100, self.process_log_queue)
    
    def log_message(self, level, message):
        """Add message to console log"""
        timestamp = datetime.now().strftime("%H:%M:%S")
        formatted_message = f"[{timestamp}] {level}: {message}\n"
        
        self.console.configure(state=tk.NORMAL)
        self.console.insert(tk.END, formatted_message)
        self.console.configure(state=tk.DISABLED)
        self.console.see(tk.END)
    
    def copy_console_content(self):
        """Copy all console content to clipboard"""
        content = self.console.get(1.0, tk.END)
        self.root.clipboard_clear()
        self.root.clipboard_append(content)
        self.log_message("INFO", "Console content copied to clipboard")
    
    def clear_console(self):
        """Clear console content"""
        self.console.configure(state=tk.NORMAL)
        self.console.delete(1.0, tk.END)
        self.console.configure(state=tk.DISABLED)
    
    def on_closing(self):
        """Handle window closing"""
        if self.running:
            if messagebox.askokcancel("Exit", "Processing is still running. Do you want to stop and exit?"):
                self.stop_comparison()
                # Wait a moment for processes to stop
                self.root.after(1000, self.root.destroy)
            return
        
        self.root.destroy()
    
    def run(self):
        """Start the application"""
        self.log_message("INFO", "Video Quality Comparison Tool started")
        self.root.mainloop()


def main():
    """Main entry point"""
    try:
        app = VideoComparator()
        app.run()
    except KeyboardInterrupt:
        print("\nApplication interrupted by user")
        sys.exit(0)
    except Exception as e:
        print(f"Fatal error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()